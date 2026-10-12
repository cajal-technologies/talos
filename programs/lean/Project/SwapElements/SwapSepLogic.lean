import Project.SwapElements.Program
import Project.SwapElements.Address
import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.SmallStepAdequacy
import CodeLib.RustStd.MemArray.SmallStep

/-! # Swap Elements — iris-lean small-step proof

The full generated call chain is proved directly with iris-lean `WP` over
`Wasm.SmallStep.Step`: func4 → func3 and func4 → func0 → func1 → func2.
Authoritative heap, global, and runtime ownership connects those rules to
closed operational `PartiallyMeets` theorems. Separate contracts cover
distinct and equal element addresses, so the alias case never duplicates an
exclusive byte owner. Concrete export executions also carry finite-trace
`SmallStep.TerminatesWith` witnesses from the executable step iterator.

Key memory facts after the swap:
  final_mem = (st.mem
    .write32(1048568, ptr)         -- func3: ptr spill
    .write32(1048572, len)         -- func3: len spill
    .write64(1048552, vA)          -- func2: temp = *ptr_a
    .write64(ptr + 8*i, vB)       -- func2: *ptr_a = *ptr_b
    .write64(ptr + 8*j, vA))      -- func2: *ptr_b = temp
  where vA = st.mem.read64(ptr + 8*i), vB = st.mem.read64(ptr + 8*j).

The spec's global0 and pages-bound preconditions are load-bearing here:
without `global 0 = 1048576` on entry, func4's scratch frame (`global 0 −
16`) could alias the array and the swap postcondition would be false. -/

/-! ## Program-specific small-step lifting rules

These rules are stated in the `Wasm.SmallStep` namespace, over the same `WP`
and total-`WP` layers as the generic lifting library, but they are proofs about
*this* program: every address, local index, and instruction below is the code
emitted for `func2` and `func3`. They therefore live next to the program they
describe rather than in `CodeLib`'s rule library.
-/

namespace Wasm.SmallStep

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

section swapElementsPartial

variable {α : Type}
variable [WasmSmallStepGS hlc α]
attribute [local instance] instWasmIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

set_option maxHeartbeats 4000000 in
/-- Call-stack-polymorphic proof of the sixteen instructions before
`Project.SwapElements.func2`'s final `ret`. The continuation receives the
updated ownership and decides whether `ret` finishes a top-level invocation or
resumes a suspended caller. -/
theorem wp_swapElementsFunc2Prefix
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB) ∗
    ▷^[16] ((globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldA ∗
      pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA) -∗
      WP (.running
        ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }} := by
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := UInt32.addSteps8 ptrA hroomA
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := UInt32.addSteps8 ptrB hroomB
  iintro ⟨⟨Hglobal, Hscratch, HA, HB⟩, Hdone⟩
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub wp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HALater : ▷ pointsTo_u64 0 (ptrA + 0) oldA $$ [HA]
  · ilater_rw_exact [UInt32.add_zero] with HA
  wasm_wp_next_bind wp_load64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) with HALater => HA
  ihave HscratchLater :
      ▷ pointsTo_u64 0 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · ilater_rw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  wasm_wp_next wp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  iintro Hscratch
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HBLater : ▷ pointsTo_u64 0 (ptrB + 0) oldB $$ [HB]
  · ilater_rw_exact [UInt32.add_zero] with HB
  wasm_wp_next_bind wp_load64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) with HBLater => HB
  ihave HALater : ▷ pointsTo_u64 0 (ptrA + 0) oldA $$ [HA]
  · ilater_rw_exact [UInt32.add_zero] with HA
  wasm_wp_next_bind wp_store64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) with HALater => HA
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HscratchLater :
      ▷ pointsTo_u64 0 ((1048544 : UInt32) + 8) oldA $$ [Hscratch]
  · ilater_rw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  wasm_wp_next wp_load64 oldA rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  iintro Hscratch
  ihave HBLater : ▷ pointsTo_u64 0 (ptrB + 0) oldB $$ [HB]
  · ilater_rw_exact [UInt32.add_zero] with HB
  wasm_wp_next_bind wp_store64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) with HBLater => HB
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

/-- Aliasing specialization of the generated exchange leaf. When both
pointers are equal there is only one exclusive eight-byte ownership token;
the two stores leave that word unchanged while the scratch word receives its
value. -/
theorem wp_swapElementsFunc2AliasPrefix
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 ptr oldValue) ∗
    ▷^[16] ((globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldValue ∗ pointsTo_u64 0 ptr oldValue) -∗
      WP (.running
        ⟨⟨[.i32 ptr, .i32 ptr], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }}) ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E {{ Φ }} := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 ptr hroom
  iintro ⟨⟨Hglobal, Hscratch, Hcell⟩, Hdone⟩
  wasm_wp_next_rebind wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub wp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HcellLater : ▷ pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · ilater_rw_exact [UInt32.add_zero] with Hcell
  wasm_wp_next_bind wp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) with HcellLater => Hcell
  ihave HscratchLater :
      ▷ pointsTo_u64 0 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · ilater_rw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  wasm_wp_next wp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  iintro Hscratch
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HcellLater : ▷ pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · ilater_rw_exact [UInt32.add_zero] with Hcell
  wasm_wp_next_bind wp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) with HcellLater => Hcell
  ihave HcellLater : ▷ pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · ilater_rw_exact [UInt32.add_zero] with Hcell
  wasm_wp_next_bind wp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) with HcellLater => Hcell
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HscratchLater :
      ▷ pointsTo_u64 0 ((1048544 : UInt32) + 8) oldValue $$ [Hscratch]
  · ilater_rw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  wasm_wp_next wp_load64 oldValue rfl rfl rfl rfl rfl rfl rfl rfl $$
    HscratchLater
  iintro Hscratch
  ihave HcellLater : ▷ pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · ilater_rw_exact [UInt32.add_zero] with Hcell
  wasm_wp_next_bind wp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) with HcellLater => Hcell
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

/-- Top-level specialization of `wp_swapElementsFunc2Prefix`. -/
theorem wp_swapElementsFunc2
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA }} := by
  iintro Hresources
  iapply wp_swapElementsFunc2Prefix ptrA ptrB oldScratch oldA oldB
    hroomA hroomB (calls := [])
  isplitl_exact Hresources
  · inext
    iintro Hresources
    wasm_wp_return_value_rfl_exact Hresources

/-- Top-level one-cell specialization for equal exchange pointers. -/
theorem wp_swapElementsFunc2Alias
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 ptr oldValue ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ptr oldValue }} := by
  iintro Hresources
  iapply wp_swapElementsFunc2AliasPrefix ptr oldScratch oldValue
    hroom (calls := [])
  isplitl_exact Hresources
  · inext
    iintro Hresources
    wasm_wp_return_value_rfl_exact Hresources

/-- Small-step Iris contract for the exact generated body of
`Project.SwapElements.func3`. It spills `len` and `ptr` into two adjacent
32-bit words and returns no Wasm values. -/
theorem wp_swapElementsFunc3
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        [ .localGet 0, .localGet 2, .store32 4,
          .localGet 0, .localGet 1, .store32 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      {{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len }} := by
  iintro ⟨Hptr, Hlen⟩
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HlenLater :
      ▷ pointsTo_u32 0 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · ilater_rw_exact [show (1048568 : UInt32) + 4 = 1048572 from rfl] with Hlen
  wasm_wp_next_bind wp_store32 oldLen rfl rfl rfl rfl with HlenLater => Hlen
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HptrLater :
      ▷ pointsTo_u32 0 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · ilater_rw_exact [UInt32.add_zero] with Hptr
  wasm_wp_next_bind wp_store32 oldPtr rfl rfl rfl rfl with HptrLater => Hptr
  wasm_wp_return_value
  isplitr_pureexact rfl
  · isplitl_rw_exact [UInt32.add_zero] with Hptr
    · irw_exact [← show (1048568 : UInt32) + 4 = 1048572 from rfl] with Hlen

end swapElementsPartial

section swapElementsTotalPrefix

variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
attribute [local instance high] activeTerminalLanguage
attribute [local instance high] activeTerminalIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

theorem twp_swapElementsFunc2Prefix
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB) ∗
    ((globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldA ∗
      pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA) -∗
      WP (.running
        ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6, ha7⟩ := UInt32.addSteps8 ptrA hroomA
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6, hb7⟩ := UInt32.addSteps8 ptrB hroomB
  iintro ⟨⟨Hglobal, Hscratch, HA, HB⟩, Hdone⟩
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub twp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave HA' : pointsTo_u64 0 (ptrA + 0) oldA $$ [HA]
  · irw_exact [UInt32.add_zero] with HA
  iapply twp_load64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) $$ HA'
  iintro HA
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · irw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  iapply twp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave HB' : pointsTo_u64 0 (ptrB + 0) oldB $$ [HB]
  · irw_exact [UInt32.add_zero] with HB
  iapply twp_load64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) $$ HB'
  iintro HB
  ihave HA' : pointsTo_u64 0 (ptrA + 0) oldA $$ [HA]
  · irw_exact [UInt32.add_zero] with HA
  iapply twp_store64 oldA (by simp)
    (by simpa using ha1) (by simpa using ha2) (by simpa using ha3)
    (by simpa using ha4) (by simpa using ha5) (by simpa using ha6)
    (by simpa using ha7) $$ HA'
  iintro HA
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldA $$ [Hscratch]
  · irw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  iapply twp_load64 oldA rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  ihave HB' : pointsTo_u64 0 (ptrB + 0) oldB $$ [HB]
  · irw_exact [UInt32.add_zero] with HB
  iapply twp_store64 oldB (by simp)
    (by simpa using hb1) (by simpa using hb2) (by simpa using hb3)
    (by simpa using hb4) (by simpa using hb5) (by simpa using hb6)
    (by simpa using hb7) $$ HB'
  iintro HB
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

theorem twp_swapElementsFunc2AliasPrefix
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296)
    {calls : List CallFrame} :
    (globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 ptr oldValue) ∗
    ((globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldValue ∗ pointsTo_u64 0 ptr oldValue) -∗
      WP (.running
        ⟨⟨[.i32 ptr, .i32 ptr], [.i32 1048544], []⟩,
          [.ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 ptr hroom
  iintro ⟨⟨Hglobal, Hscratch, Hcell⟩, Hdone⟩
  wasm_twp_rebind twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub twp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · irw_exact [UInt32.add_zero] with Hcell
  iapply twp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldScratch $$ [Hscratch]
  · irw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  iapply twp_store64 oldScratch rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · irw_exact [UInt32.add_zero] with Hcell
  iapply twp_load64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · irw_exact [UInt32.add_zero] with Hcell
  iapply twp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hscratch' :
      pointsTo_u64 0 ((1048544 : UInt32) + 8) oldValue $$ [Hscratch]
  · irw_exact [show (1048544 : UInt32) + 8 = 1048552 from rfl] with Hscratch
  iapply twp_load64 oldValue rfl rfl rfl rfl rfl rfl rfl rfl $$
    Hscratch'
  iintro Hscratch
  ihave Hcell' : pointsTo_u64 0 (ptr + 0) oldValue $$ [Hcell]
  · irw_exact [UInt32.add_zero] with Hcell
  iapply twp_store64 oldValue (by simp)
    (by simpa using h1) (by simpa using h2) (by simpa using h3)
    (by simpa using h4) (by simpa using h5) (by simpa using h6)
    (by simpa using h7) $$ Hcell'
  iintro Hcell
  iapply Hdone
  simp only [UInt32.add_zero, UInt32.reduceAdd]
  iframe

end swapElementsTotalPrefix

section swapElementsTotal

variable [WasmSmallStepGS hlc α]
local instance instWasmSwapTotalIrisGS :
    IrisGS_gen hlc (Expr α) (WasmHeapGF α) :=
  instIrisGS
variable {s : Stuckness} {E : CoPset}
variable {Φ : List Value → IProp (WasmHeapGF α)}

theorem twp_swapElementsFunc2
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB ⊢
    WP (.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA }] := by
  iintro Hresources
  iapply twp_swapElementsFunc2Prefix ptrA ptrB oldScratch oldA oldB
    hroomA hroomB (calls := [])
  isplitl_exact Hresources
  · iintro Hresources
    iapply twp_returnFromFunction
    simp only [List.take, List.nil_append]
    iapply twp.value rfl
    isplitr_pureexact rfl
    · iexact Hresources

theorem twp_swapElementsFunc2Alias
    (ptr : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ptr.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 ptr oldValue ⊢
    WP (.running
      ⟨⟨[.i32 ptr, .i32 ptr], [.i32 0], []⟩,
        [ .globalGet 0, .const 16, .sub, .localSet 2,
          .localGet 2, .localGet 0, .load64 0, .store64 8,
          .localGet 0, .localGet 1, .load64 0, .store64 0,
          .localGet 1, .localGet 2, .load64 8, .store64 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ptr oldValue }] := by
  iintro Hresources
  iapply twp_swapElementsFunc2AliasPrefix ptr oldScratch oldValue hroom
    (calls := [])
  isplitl_exact Hresources
  · iintro Hresources
    iapply twp_returnFromFunction
    simp only [List.take, List.nil_append]
    iapply twp.value rfl
    isplitr_pureexact rfl
    · iexact Hresources

theorem twp_swapElementsFunc3
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        [ .localGet 0, .localGet 2, .store32 4,
          .localGet 0, .localGet 1, .store32 0, .ret ],
        0, [], [], []⟩ : Expr α) @ s; E
      [{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len }] := by
  iintro ⟨Hptr, Hlen⟩
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hlen' :
      pointsTo_u32 0 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · irw_exact [show (1048568 : UInt32) + 4 = 1048572 from rfl] with Hlen
  wasm_twp_bind twp_store32 oldLen rfl rfl rfl rfl with Hlen' => Hlen
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hptr' :
      pointsTo_u32 0 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · irw_exact [UInt32.add_zero] with Hptr
  wasm_twp_bind twp_store32 oldPtr rfl rfl rfl rfl with Hptr' => Hptr
  iapply twp_returnFromFunction
  simp only [List.take, List.nil_append]
  iapply twp.value rfl
  isplitr_pureexact rfl
  · isplitl_rw_exact [UInt32.add_zero] with Hptr
    · irw_exact [← show (1048568 : UInt32) + 4 = 1048572 from rfl] with Hlen

end swapElementsTotal

end Wasm.SmallStep

namespace Project.SwapElements.SwapSepLogic

open Iris Iris.ProgramLogic Language.Notation Std
open Wasm Wasm.SmallStep Wasm.SepLogic

set_option maxRecDepth 1048576

private def func1OuterBody : Program :=
  match func1 with
  | .block _ _ body _ _ :: _ => body
  | _ => []

private def func1OuterContinuation : Program :=
  match func1 with
  | .block _ _ _ _ _ :: continuation => continuation
  | _ => []

private def func1OuterFrame : Wasm.SmallStep.ControlFrame :=
  { kind := .block
    paramArity := 0
    resultArity := 0
    body := func1OuterBody
    continuation := func1OuterContinuation
    belowStack := [] }

set_option maxHeartbeats 4000000 in
/-- The exact successful bounds-check prefix of generated `func1`. After
twenty-eight instruction-level transitions, `i < len` and `j < len` select the
outward branch to the real `call 2` continuation and leave `&arr[i]` in local
slot five and `&arr[j]` on the operand stack. -/
theorem func1_happyPrefix_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (ptr len i j : UInt32) (hi : i < len) (hj : j < len)
    (calls : List Wasm.SmallStep.CallFrame) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    ▷^[28] WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 addressI], [.i32 addressJ, .i32 addressI]⟩,
        [.call 2, .ret], 0, [], [func1OuterFrame], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro Htarget
  simp only [func1]
  wasm_wp_pures [wp_block wp_block wp_block wp_localGet wp_localGet]
  wasm_wp_next Wasm.SmallStep.wp_ltU (result := 1) (by simp [hi])
  wasm_wp_pures [wp_const wp_and] rewriting [show (1 &&& 1 : UInt32) = 1 by decide]
  wasm_wp_next Wasm.SmallStep.wp_eqz (value := 1) (result := 0) rfl
  wasm_wp_pures [wp_brIfZero wp_localGet wp_localGet wp_const wp_shl wp_add wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_localGet]
  wasm_wp_next Wasm.SmallStep.wp_ltU (result := 1) (by simp [hj])
  wasm_wp_pures [wp_const wp_and] rewriting [show (1 &&& 1 : UInt32) = 1 by decide]
  wasm_wp_next Wasm.SmallStep.wp_brIf (by decide) rfl
  simp only [List.take_nil, List.drop_nil, List.nil_append]
  wasm_wp_pures [wp_localGet wp_localGet wp_localGet wp_const wp_shl wp_add]
  simp only [func1OuterFrame, func1OuterBody, func1OuterContinuation, func1]
  iexact Htarget

/-- The generated `call 2` transition reached by
`func1_happyPrefix_smallStep_wp`. Runtime ownership proves that function index
two is the concrete generated `func2Def`, and the installed call frame retains
the outer bounds-check frame and `func1`'s final return continuation. -/
theorem func1_call2_entry_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (ptr len i j : UInt32) (calls : List Wasm.SmallStep.CallFrame) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    ▷ runtimeModuleOwn ⟨0⟩ «module» -∗
    ▷ (runtimeModuleOwn ⟨0⟩ «module» -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 addressI, .i32 addressJ], [.i32 0], []⟩,
          func2, 0, [], [],
          { locals :=
              ⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
                [.i32 addressI], []⟩
            continuation := [.ret]
            resultArity := 0
            callerRemainder := []
            control := [func1OuterFrame]
            returningInstance := ⟨0⟩ } :: calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) -∗
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 addressI], [.i32 addressJ, .i32 addressI]⟩,
        [.call 2, .ret], 0, [], [func1OuterFrame], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  simpa [func2Def, Function.toLocals, Function.numParams, ValueType.zero] using
    (Wasm.SmallStep.wp_call (α := Unit) (s := s) (E := E)
      (Φ := Φ)
      (params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604])
      (localValues := [.i32 ((i <<< (3 % 32)) + ptr)])
      (values :=
        [.i32 ((j <<< (3 % 32)) + ptr),
          .i32 ((i <<< (3 % 32)) + ptr)])
      (code := [.ret]) (arity := 0) (remainder := [])
      (controls := [func1OuterFrame]) (calls := calls)
      «module» 2 func2Def (by decide) rfl ⟨0⟩)

/-- The generated exchange leaf executed beneath `func1`'s concrete call
frame. Its final `ret` resumes `func1`, whose own final `ret` then completes
the top-level invocation. -/
theorem func2_in_func1_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    {ri : Wasm.SmallStep.ModuleInstanceId}
    (hreturn :
      runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    let caller : Wasm.SmallStep.CallFrame :=
      { locals :=
          ⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 addressI], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [func1OuterFrame]
        returningInstance := ri }
    runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 addressI oldA ∗ pointsTo_u64 0 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 addressI, .i32 addressJ], [.i32 0], []⟩,
        func2, 0, [], [], caller :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Hruntime, HR, Hresources⟩
  simp only [func2]
  iapply Wasm.SmallStep.wp_swapElementsFunc2Prefix
    ((i <<< (3 % 32)) + ptr) ((j <<< (3 % 32)) + ptr)
    oldScratch oldA oldB hroomI hroomJ
  isplitl_exact Hresources
  · inext
    iintro Hresources
    wasm_wp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

/-- Equal-index counterpart of `func2_in_func1_context_smallStep_wp`. The
callee receives the same pointer twice, so one array-word owner is threaded
sequentially through both loads and stores. -/
theorem func2Alias_in_func1_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    {ri : Wasm.SmallStep.ModuleInstanceId}
    (hreturn :
      runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    let address := (i <<< (3 % 32)) + ptr
    runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 address oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 address, .i32 address], [.i32 0], []⟩,
        func2, 0, [], [], {
          locals :=
            ⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
              [.i32 address], []⟩
          continuation := [.ret]
          resultArity := 0
          callerRemainder := []
          control := [func1OuterFrame]
          returningInstance := ri } :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨Hruntime, HR, Hresources⟩
  simp only [func2]
  iapply Wasm.SmallStep.wp_swapElementsFunc2AliasPrefix
    ((i <<< (3 % 32)) + ptr) oldScratch oldValue hroom
  isplitl_exact Hresources
  · inext
    iintro Hresources
    wasm_wp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

/-- Successful equal-index path of the generated bounds-checking wrapper. -/
theorem func1_alias_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hresources⟩
  wasm_wp_next func1_happyPrefix_smallStep_wp ptr len i i hi hi calls
  wasm_wp_next_rebind func1_call2_entry_smallStep_wp ptr len i i calls with Hruntime
  iapply_then_frame func2Alias_in_func1_context_smallStep_wp R
      ptr len i oldScratch oldValue hroom calls =>
    iintro ⟨Hruntime, HR, Hresources⟩
    iapply_frame hreturn

/-- Call-stack-polymorphic happy path of generated `func1`. The theorem stops
at `func1`'s own final return, allowing callers to choose whether that return
completes the execution or resumes another generated frame. -/
theorem func1_happy_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 addressI oldA ∗ pointsTo_u64 0 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  dsimp only
  iintro ⟨HR, Hruntime, Hresources⟩
  wasm_wp_next func1_happyPrefix_smallStep_wp ptr len i j hi hj calls
  wasm_wp_next_rebind func1_call2_entry_smallStep_wp ptr len i j calls with Hruntime
  iapply_then_frame func2_in_func1_context_smallStep_wp R
      ptr len i j oldScratch oldA oldB hroomI hroomJ calls =>
    iintro ⟨Hruntime, HR, Hresources⟩
    iapply_frame hreturn

/-- End-to-end happy path of generated `func1`: both bounds checks succeed,
the physical-runtime-checked direct call enters `func2`, the three words are
exchanged, and both administrative returns are discharged. -/
theorem func1_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 addressI oldA ∗ pointsTo_u64 0 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 addressI oldB ∗ pointsTo_u64 0 addressJ oldA }} := by
  dsimp only
  iintro Hresources
  iapply func1_happy_context_smallStep_wp (iprop(True))
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ []
  iintro ⟨_Htrue, Hruntime, Hresources⟩
  iclear Hruntime
  wasm_wp_return_value_rfl_exact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-- The generated `func0` forwarding wrapper, composed through its real direct
call frame. This remains contextual so the exported wrapper can suspend above
it without duplicating any semantics. -/
theorem func0_happy_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
        func0, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hresources⟩
  simp only [func0]
  wasm_wp_pures [wp_localGet wp_localGet wp_localGet wp_localGet wp_const]
  wasm_wp_next_rebind Wasm.SmallStep.wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp only [func1Def, Function.toLocals, Function.numParams,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.take, List.drop,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map, ValueType.zero]
  iapply_then_frame func1_happy_context_smallStep_wp R
      ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ _ =>
    iintro ⟨HR, Hruntime, Hmem⟩
    wasm_wp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

/-- Equal-index path of the generated forwarding wrapper. -/
theorem func0_alias_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
        func0, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hruntime, Hresources⟩
  simp only [func0]
  wasm_wp_pures [wp_localGet wp_localGet wp_localGet wp_localGet wp_const]
  wasm_wp_next_rebind Wasm.SmallStep.wp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp only [func1Def, Function.toLocals, Function.numParams,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.take, List.drop,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map, ValueType.zero]
  iapply_then_frame func1_alias_context_smallStep_wp R
      ptr len i oldScratch oldValue hi hroom _ =>
    iintro ⟨HR, Hruntime, Hmem⟩
    wasm_wp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

/-- Top-level equal-index forwarding-wrapper contract. -/
theorem func0_alias_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
        func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue }} := by
  iintro Hresources
  iapply func0_alias_context_smallStep_wp (iprop(True))
    ptr len i oldScratch oldValue hi hroom []
  · iintro ⟨_Htrue, Hruntime, Hresources⟩
    iclear Hruntime
    wasm_wp_return_value_rfl_exact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-- Closed-WP form of the generated forwarding wrapper. -/
theorem func0_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
        func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA }} := by
  iintro Hresources
  iapply func0_happy_context_smallStep_wp (iprop(True))
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ []
  iintro ⟨_Htrue, Hruntime, Hresources⟩
  iclear Hruntime
  wasm_wp_return_value_rfl_exact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

/-- Small-step Iris proof for the generated `func2` exchange leaf. Global 0
selects its scratch frame, while authoritative eight-byte ownership connects
all three physical words to the operational `load64`/`store64` steps. -/
theorem func2_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        func2, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA }} := by
  simpa only [func2] using
    (Wasm.SmallStep.wp_swapElementsFunc2
      (α := Unit) (s := s) (E := E)
      ptrA ptrB oldScratch oldA oldB hroomA hroomB)

/-- Small-step Iris proof for the generated `func3` leaf. This is the first
downstream swap proof that uses iris-lean's `WP` over `Wasm.SmallStep.Step`. -/
theorem func3_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (oldPtr oldLen ptr len : UInt32)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }}) :
    R ∗ pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E {{ Φ }} := by
  iintro ⟨HR, Hptr, Hlen⟩
  simp only [func3]
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HlenLater :
      ▷ pointsTo_u32 0 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · ilater_rw_exact [show (1048568 : UInt32) + 4 = 1048572 from rfl] with Hlen
  wasm_wp_next_bind Wasm.SmallStep.wp_store32 oldLen rfl rfl rfl rfl with HlenLater => Hlen
  wasm_wp_pures [wp_localGet wp_localGet]
  ihave HptrLater :
      ▷ pointsTo_u32 0 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · ilater_rw_exact [UInt32.add_zero] with Hptr
  wasm_wp_next_bind Wasm.SmallStep.wp_store32 oldPtr rfl rfl rfl rfl with HptrLater => Hptr
  iapply hreturn
  rw [UInt32.add_zero,
    ← show (1048568 : UInt32) + 4 = 1048572 from rfl]
  iframe

theorem func3_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len }} := by
  simpa only [func3] using
    (Wasm.SmallStep.wp_swapElementsFunc3
      (α := Unit) (s := s) (E := E) oldPtr oldLen ptr len)

/-- Successful exported path through the generated stack frame, spill helper,
forwarding wrapper, bounds checks, and exchange leaf. The postcondition keeps
the complete touched footprint so the subsequent adequacy theorem can connect
every ghost cell back to physical Wasm memory. -/
theorem func4_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i j oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA }} := by
  iintro ⟨Hruntime, Hglobal, Hscratch, HspillPtr, HspillLen, HA, HB⟩
  simp only [func4]
  wasm_wp_next_rebind Wasm.SmallStep.wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub wp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_wp_pures [wp_localGet]
  ihave HglobalLater : ▷ globalPointsToAt 0 0 (.i32 1048576) $$ [Hglobal]
  · ilater_exact Hglobal
  wasm_wp_next_bind Wasm.SmallStep.wp_globalSet with HglobalLater => Hglobal
  wasm_wp_pures [wp_const wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_const wp_add wp_localGet wp_localGet wp_localGet]
  wasm_wp_next_rebind Wasm.SmallStep.wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply func3_context_smallStep_wp
    (iprop% runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB)
    oldSpillPtr oldSpillLen ptr len _
  · iintro ⟨Hrest, HspillPtr, HspillLen⟩
    icases Hrest with ⟨Hruntime, Hglobal, Hscratch, HA, HB⟩
    wasm_wp_return_from_call Hruntime [List.take, List.nil_append]
    wasm_wp_pures [wp_localGet]
    ihave HlenLater :
        ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) len $$ [HspillLen]
    · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with HspillLen
    wasm_wp_next_bind Wasm.SmallStep.wp_load32 len
      (by decide) (by decide) (by decide) (by decide) with HlenLater => HspillLen
    wasm_wp_localSet
    wasm_wp_pures [wp_localGet]
    ihave HptrLater :
        ▷ pointsTo_u32 0 ((1048560 : UInt32) + 8) ptr $$ [HspillPtr]
    · ilater_rw_exact [show (1048560 : UInt32) + 8 = 1048568 by decide] with HspillPtr
    wasm_wp_next_bind Wasm.SmallStep.wp_load32 ptr
      (by decide) (by decide) (by decide) (by decide) with HptrLater => HspillPtr
    wasm_wp_pures [wp_localGet wp_localGet wp_localGet]
    wasm_wp_next_rebind Wasm.SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func0Def, Function.toLocals, Function.numParams]
    iapply func0_happy_context_smallStep_wp
      (iprop% pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len)
      ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ _
    · iintro ⟨⟨HspillPtr, HspillLen⟩,
        Hruntime, Hglobal, Hscratch, HA, HB⟩
      wasm_wp_next Wasm.SmallStep.wp_returnFromCallExplicit $$ Hruntime
      simp only [List.take, List.nil_append]
      wasm_wp_pures [wp_localGet wp_const wp_add]
      ihave HglobalLater :
          ▷ globalPointsToAt 0 0 (.i32 1048560) $$ [Hglobal]
      · ilater_exact Hglobal
      wasm_wp_next_bind Wasm.SmallStep.wp_globalSet with HglobalLater => Hglobal
      rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
      rw [show (3 % 32 : UInt32) = 3 by decide]
      wasm_wp_return_value
      isplitr_pureexact rfl
      · iframe
    · rw [show (3 % 32 : UInt32) = 3 by decide]
      iframe
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iframe

/-- Equal-index exported path. The generated stack-frame mechanics are
identical to `func4_happy_smallStep_wp`, but the nested exchange uses the
one-cell alias contract. -/
theorem func4_alias_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      {{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue }} := by
  iintro ⟨Hruntime, Hglobal, Hscratch, HspillPtr, HspillLen, Hcell⟩
  simp only [func4]
  wasm_wp_next_rebind Wasm.SmallStep.wp_globalGet with Hglobal
  wasm_wp_pures [wp_const wp_sub wp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_wp_pures [wp_localGet]
  ihave HglobalLater : ▷ globalPointsToAt 0 0 (.i32 1048576) $$ [Hglobal]
  · ilater_exact Hglobal
  wasm_wp_next_bind Wasm.SmallStep.wp_globalSet with HglobalLater => Hglobal
  wasm_wp_pures [wp_const wp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_wp_pures [wp_localGet wp_const wp_add wp_localGet wp_localGet wp_localGet]
  wasm_wp_next_rebind Wasm.SmallStep.wp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply func3_context_smallStep_wp
    (iprop% runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue)
    oldSpillPtr oldSpillLen ptr len _
  · iintro ⟨Hrest, HspillPtr, HspillLen⟩
    icases Hrest with ⟨Hruntime, Hglobal, Hscratch, Hcell⟩
    wasm_wp_return_from_call Hruntime [List.take, List.nil_append]
    wasm_wp_pures [wp_localGet]
    ihave HlenLater :
        ▷ pointsTo_u32 0 ((1048560 : UInt32) + 12) len $$ [HspillLen]
    · ilater_rw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with HspillLen
    wasm_wp_next_bind Wasm.SmallStep.wp_load32 len
      (by decide) (by decide) (by decide) (by decide) with HlenLater => HspillLen
    wasm_wp_localSet
    wasm_wp_pures [wp_localGet]
    ihave HptrLater :
        ▷ pointsTo_u32 0 ((1048560 : UInt32) + 8) ptr $$ [HspillPtr]
    · ilater_rw_exact [show (1048560 : UInt32) + 8 = 1048568 by decide] with HspillPtr
    wasm_wp_next_bind Wasm.SmallStep.wp_load32 ptr
      (by decide) (by decide) (by decide) (by decide) with HptrLater => HspillPtr
    wasm_wp_pures [wp_localGet wp_localGet wp_localGet]
    wasm_wp_next_rebind Wasm.SmallStep.wp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func0Def, Function.toLocals, Function.numParams]
    iapply func0_alias_context_smallStep_wp
      (iprop% pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len)
      ptr len i oldScratch oldValue hi hroom _
    · iintro ⟨⟨HspillPtr, HspillLen⟩,
        Hruntime, Hglobal, Hscratch, Hcell⟩
      wasm_wp_next Wasm.SmallStep.wp_returnFromCallExplicit $$ Hruntime
      simp only [List.take, List.nil_append]
      wasm_wp_pures [wp_localGet wp_const wp_add]
      ihave HglobalLater :
          ▷ globalPointsToAt 0 0 (.i32 1048560) $$ [Hglobal]
      · ilater_exact Hglobal
      wasm_wp_next_bind Wasm.SmallStep.wp_globalSet with HglobalLater => Hglobal
      rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
      rw [show (3 % 32 : UInt32) = 3 by decide]
      wasm_wp_return_value
      isplitr_pureexact rfl
      · iframe
    · rw [show (3 % 32 : UInt32) = 3 by decide]
      iframe
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iframe

/-! ## TWP counterparts of the small-step WP theorems -/

set_option maxHeartbeats 4000000 in
theorem twp_func1_happyPrefix_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (ptr len i j : UInt32) (hi : i < len) (hj : j < len)
    (calls : List Wasm.SmallStep.CallFrame) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 addressI], [.i32 addressJ, .i32 addressI]⟩,
        [.call 2, .ret], 0, [], [func1OuterFrame], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  dsimp only
  iintro Htarget
  simp only [func1]
  wasm_twp_pures [twp_block twp_block twp_block twp_localGet twp_localGet]
  iapply Wasm.SmallStep.twp_ltU (result := 1) (by simp [hi])
  wasm_twp_pures [twp_const twp_and] rewriting [show (1 &&& 1 : UInt32) = 1 by decide]
  iapply Wasm.SmallStep.twp_eqz (value := 1) (result := 0) rfl
  wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet twp_const twp_shl twp_add twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  iapply Wasm.SmallStep.twp_ltU (result := 1) (by simp [hj])
  wasm_twp_pures [twp_const twp_and] rewriting [show (1 &&& 1 : UInt32) = 1 by decide]
  iapply Wasm.SmallStep.twp_brIf (by decide) rfl
  simp only [List.take_nil, List.drop_nil, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_const twp_shl twp_add]
  simp only [func1OuterFrame, func1OuterBody, func1OuterContinuation, func1]
  iexact Htarget

theorem twp_func1_call2_entry_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (ptr len i j : UInt32) (calls : List Wasm.SmallStep.CallFrame) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    let caller : Wasm.SmallStep.CallFrame :=
      { locals :=
          ⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 addressI], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [func1OuterFrame]
        returningInstance := ⟨0⟩ }
    runtimeModuleOwn ⟨0⟩ «module» -∗
    (runtimeModuleOwn ⟨0⟩ «module» -∗
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 addressI, .i32 addressJ], [.i32 0], []⟩,
          func2, 0, [], [], caller :: calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) -∗
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 addressI], [.i32 addressJ, .i32 addressI]⟩,
        [.call 2, .ret], 0, [], [func1OuterFrame], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  dsimp only
  simpa [func2Def, Function.toLocals, Function.numParams, ValueType.zero] using
    (Wasm.SmallStep.twp_call (α := Unit) (s := s) (E := E)
      (Φ := Φ)
      (params := [.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604])
      (localValues := [.i32 ((i <<< (3 % 32)) + ptr)])
      (values :=
        [.i32 ((j <<< (3 % 32)) + ptr),
          .i32 ((i <<< (3 % 32)) + ptr)])
      (code := [.ret]) (arity := 0) (remainder := [])
      (controls := [func1OuterFrame]) (calls := calls)
      «module» 2 func2Def (by decide) rfl ⟨0⟩)

theorem twp_func2_in_func1_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    {ri : Wasm.SmallStep.ModuleInstanceId}
    (hreturn :
      runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    let caller : Wasm.SmallStep.CallFrame :=
      { locals :=
          ⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 addressI], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [func1OuterFrame]
        returningInstance := ri }
    runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 addressI oldA ∗ pointsTo_u64 0 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 addressI, .i32 addressJ], [.i32 0], []⟩,
        func2, 0, [], [], caller :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  dsimp only
  iintro ⟨Hruntime, HR, Hresources⟩
  simp only [func2]
  iapply Wasm.SmallStep.twp_swapElementsFunc2Prefix
    ((i <<< (3 % 32)) + ptr) ((j <<< (3 % 32)) + ptr)
    oldScratch oldA oldB hroomI hroomJ
  isplitl_exact Hresources
  · iintro Hresources
    wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

theorem twp_func2Alias_in_func1_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    {ri : Wasm.SmallStep.ModuleInstanceId}
    (hreturn :
      runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    let address := (i <<< (3 % 32)) + ptr
    runtimeModuleOwn ri «module» ∗ R ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗ pointsTo_u64 0 address oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 address, .i32 address], [.i32 0], []⟩,
        func2, 0, [], [], {
          locals :=
            ⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
              [.i32 address], []⟩
          continuation := [.ret]
          resultArity := 0
          callerRemainder := []
          control := [func1OuterFrame]
          returningInstance := ri } :: calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  dsimp only
  iintro ⟨Hruntime, HR, Hresources⟩
  simp only [func2]
  iapply Wasm.SmallStep.twp_swapElementsFunc2AliasPrefix
    ((i <<< (3 % 32)) + ptr) oldScratch oldValue hroom
  isplitl_exact Hresources
  · iintro Hresources
    wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

theorem twp_func1_alias_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hresources⟩
  iapply twp_func1_happyPrefix_smallStep_wp ptr len i i hi hi calls
  wasm_twp_rebind twp_func1_call2_entry_smallStep_wp ptr len i i calls with Hruntime
  iapply_then_frame twp_func2Alias_in_func1_context_smallStep_wp R
      ptr len i oldScratch oldValue hroom calls =>
    iintro ⟨Hruntime, HR, Hresources⟩
    iapply_frame hreturn

theorem twp_func1_happy_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
            [.i32 ((i <<< (3 % 32)) + ptr)], []⟩,
          [.ret], 0, [], [func1OuterFrame], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 addressI oldA ∗ pointsTo_u64 0 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], calls⟩ : Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  dsimp only
  iintro ⟨HR, Hruntime, Hresources⟩
  iapply twp_func1_happyPrefix_smallStep_wp ptr len i j hi hj calls
  wasm_twp_rebind twp_func1_call2_entry_smallStep_wp ptr len i j calls with Hruntime
  iapply_then_frame twp_func2_in_func1_context_smallStep_wp R
      ptr len i j oldScratch oldA oldB hroomI hroomJ calls =>
    iintro ⟨Hruntime, HR, Hresources⟩
    iapply_frame hreturn

theorem twp_func1_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    let addressI := (i <<< (3 % 32)) + ptr
    let addressJ := (j <<< (3 % 32)) + ptr
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 addressI oldA ∗ pointsTo_u64 0 addressJ oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j, .i32 1048604],
          [.i32 0], []⟩,
        func1, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 addressI oldB ∗ pointsTo_u64 0 addressJ oldA }] := by
  dsimp only
  iintro Hresources
  iapply twp_func1_happy_context_smallStep_wp (iprop(True))
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ []
  iintro ⟨_Htrue, Hruntime, Hresources⟩
  iclear Hruntime
  iapply Wasm.SmallStep.twp_returnFromFunction
  simp only [List.take, List.nil_append]
  iapply twp.value rfl
  isplitr_pureexact rfl
  · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

theorem twp_func0_happy_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
        func0, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hresources⟩
  simp only [func0]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_const]
  wasm_twp_rebind Wasm.SmallStep.twp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp only [func1Def, Function.toLocals, Function.numParams,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.take, List.drop,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map, ValueType.zero]
  iapply_then_frame twp_func1_happy_context_smallStep_wp R
      ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ _ =>
    iintro ⟨HR, Hruntime, Hmem⟩
    wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

theorem twp_func0_alias_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    R ∗ runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
        func0, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hruntime, Hresources⟩
  simp only [func0]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet twp_const]
  wasm_twp_rebind Wasm.SmallStep.twp_call «module» 1 func1Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp only [func1Def, Function.toLocals, Function.numParams,
    List.length_cons, List.length_nil, Nat.reduceAdd, List.take, List.drop,
    List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append, List.map, ValueType.zero]
  iapply_then_frame twp_func1_alias_context_smallStep_wp R
      ptr len i oldScratch oldValue hi hroom _ =>
    iintro ⟨HR, Hruntime, Hmem⟩
    wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
    iapply_frame hreturn

theorem twp_func0_alias_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i : UInt32) (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i], [], []⟩,
        func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue }] := by
  iintro Hresources
  iapply twp_func0_alias_context_smallStep_wp (iprop(True))
    ptr len i oldScratch oldValue hi hroom []
  · iintro ⟨_Htrue, Hruntime, Hresources⟩
    iclear Hruntime
    iapply Wasm.SmallStep.twp_returnFromFunction
    simp only [List.take, List.nil_append]
    iapply twp.value rfl
    isplitr_pureexact rfl
    · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

theorem twp_func0_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i j : UInt32) (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j], [], []⟩,
        func0, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA }] := by
  iintro Hresources
  iapply twp_func0_happy_context_smallStep_wp (iprop(True))
    ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ []
  iintro ⟨_Htrue, Hruntime, Hresources⟩
  iclear Hruntime
  iapply Wasm.SmallStep.twp_returnFromFunction
  simp only [List.take, List.nil_append]
  iapply twp.value rfl
  isplitr_pureexact rfl
  · iexact Hresources
  · isplitr
    · itrivial
    · iexact Hresources

theorem twp_func2_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptrA ptrB : UInt32) (oldScratch oldA oldB : UInt64)
    (hroomA : ptrA.toNat + 8 ≤ 4294967296)
    (hroomB : ptrB.toNat + 8 ≤ 4294967296) :
    globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ptrA oldA ∗ pointsTo_u64 0 ptrB oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptrA, .i32 ptrB], [.i32 0], []⟩,
        func2, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048560) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u64 0 ptrA oldB ∗ pointsTo_u64 0 ptrB oldA }] := by
  simpa only [func2] using
    (Wasm.SmallStep.twp_swapElementsFunc2
      (α := Unit) (s := s) (E := E)
      ptrA ptrB oldScratch oldA oldB hroomA hroomB)

theorem twp_func3_context_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp (WasmHeapGF Unit)}
    (R : IProp (WasmHeapGF Unit))
    (oldPtr oldLen ptr len : UInt32)
    (calls : List Wasm.SmallStep.CallFrame)
    (hreturn :
      R ∗ pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ⊢
      WP (Wasm.SmallStep.Expr.running
        ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
          [.ret], 0, [], [], calls⟩ :
          Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }]) :
    R ∗ pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], calls⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E [{ Φ }] := by
  iintro ⟨HR, Hptr, Hlen⟩
  simp only [func3]
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hlen' :
      pointsTo_u32 0 ((1048568 : UInt32) + 4) oldLen $$ [Hlen]
  · irw_exact [show (1048568 : UInt32) + 4 = 1048572 from rfl] with Hlen
  wasm_twp_bind Wasm.SmallStep.twp_store32 oldLen rfl rfl rfl rfl with Hlen' => Hlen
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hptr' :
      pointsTo_u32 0 ((1048568 : UInt32) + 0) oldPtr $$ [Hptr]
  · irw_exact [UInt32.add_zero] with Hptr
  wasm_twp_bind Wasm.SmallStep.twp_store32 oldPtr rfl rfl rfl rfl with Hptr' => Hptr
  iapply hreturn
  rw [UInt32.add_zero,
    ← show (1048568 : UInt32) + 4 = 1048572 from rfl]
  iframe

theorem twp_func3_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (oldPtr oldLen ptr len : UInt32) :
    pointsTo_u32 0 1048568 oldPtr ∗ pointsTo_u32 0 1048572 oldLen ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], []⟩ : Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len }] := by
  simpa only [func3] using
    (Wasm.SmallStep.twp_swapElementsFunc3
      (α := Unit) (s := s) (E := E) oldPtr oldLen ptr len)

set_option maxHeartbeats 4000000 in
theorem twp_func4_happy_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i j oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u64 0 1048552 oldA ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldB ∗
        pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldA }] := by
  iintro ⟨Hruntime, Hglobal, Hscratch, HspillPtr, HspillLen, HA, HB⟩
  simp only [func4]
  wasm_twp_rebind Wasm.SmallStep.twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub twp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_globalSet with Hglobal
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply twp_func3_context_smallStep_wp
    (iprop% runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB)
    oldSpillPtr oldSpillLen ptr len _
  · iintro ⟨Hrest, HspillPtr, HspillLen⟩
    icases Hrest with ⟨Hruntime, Hglobal, Hscratch, HA, HB⟩
    wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
    wasm_twp_pures [twp_localGet]
    ihave HspillLen' :
        pointsTo_u32 0 ((1048560 : UInt32) + 12) len $$ [HspillLen]
    · irw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with HspillLen
    wasm_twp_bind Wasm.SmallStep.twp_load32 len
      (by decide) (by decide) (by decide) (by decide) with HspillLen' => HspillLen
    wasm_twp_localSet
    wasm_twp_pures [twp_localGet]
    ihave HspillPtr' :
        pointsTo_u32 0 ((1048560 : UInt32) + 8) ptr $$ [HspillPtr]
    · irw_exact [show (1048560 : UInt32) + 8 = 1048568 by decide] with HspillPtr
    wasm_twp_bind Wasm.SmallStep.twp_load32 ptr
      (by decide) (by decide) (by decide) (by decide) with HspillPtr' => HspillPtr
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func0Def, Function.toLocals, Function.numParams]
    iapply twp_func0_happy_context_smallStep_wp
      (iprop% pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len)
      ptr len i j oldScratch oldA oldB hi hj hroomI hroomJ _
    · iintro ⟨⟨HspillPtr, HspillLen⟩,
        Hruntime, Hglobal, Hscratch, HA, HB⟩
      wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      wasm_twp_rebind Wasm.SmallStep.twp_globalSet with Hglobal
      rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
      rw [show (3 % 32 : UInt32) = 3 by decide]
      iapply Wasm.SmallStep.twp_returnFromFunction
      simp only [List.take, List.nil_append]
      iapply twp.value rfl
      isplitr_pureexact rfl
      · iframe
    · rw [show (3 % 32 : UInt32) = 3 by decide]
      iframe
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iframe

set_option maxHeartbeats 4000000 in
theorem twp_func4_alias_smallStep_wp
    [Wasm.SmallStep.WasmSmallStepGS hlc Unit]
    {s : Stuckness} {E : CoPset}
    (ptr len i oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296) :
    runtimeModuleOwn ⟨0⟩ «module» ∗
      globalPointsToAt 0 0 (.i32 1048576) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue ⊢
    WP (Wasm.SmallStep.Expr.running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 i],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩ :
        Wasm.SmallStep.Expr Unit) @ s; E
      [{ result, ⌜result = []⌝ ∗
        globalPointsToAt 0 0 (.i32 1048576) ∗
        pointsTo_u64 0 1048552 oldValue ∗
        pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
        pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue }] := by
  iintro ⟨Hruntime, Hglobal, Hscratch, HspillPtr, HspillLen, Hcell⟩
  simp only [func4]
  wasm_twp_rebind Wasm.SmallStep.twp_globalGet with Hglobal
  wasm_twp_pures [twp_const twp_sub twp_localSet]
  simp only [UInt32.reduceSub, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_globalSet with Hglobal
  wasm_twp_pures [twp_const twp_localSet]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_call «module» 3 func3Def
    (by simp [«module»]) (by simp [«module»]) with Hruntime
  simp [func3Def, Function.toLocals, Function.numParams]
  iapply twp_func3_context_smallStep_wp
    (iprop% runtimeModuleOwn ⟨0⟩ «module» ∗ globalPointsToAt 0 0 (.i32 1048560) ∗
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue)
    oldSpillPtr oldSpillLen ptr len _
  · iintro ⟨Hrest, HspillPtr, HspillLen⟩
    icases Hrest with ⟨Hruntime, Hglobal, Hscratch, Hcell⟩
    wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
    wasm_twp_pures [twp_localGet]
    ihave HspillLen' :
        pointsTo_u32 0 ((1048560 : UInt32) + 12) len $$ [HspillLen]
    · irw_exact [show (1048560 : UInt32) + 12 = 1048572 by decide] with HspillLen
    wasm_twp_bind Wasm.SmallStep.twp_load32 len
      (by decide) (by decide) (by decide) (by decide) with HspillLen' => HspillLen
    wasm_twp_localSet
    wasm_twp_pures [twp_localGet]
    ihave HspillPtr' :
        pointsTo_u32 0 ((1048560 : UInt32) + 8) ptr $$ [HspillPtr]
    · irw_exact [show (1048560 : UInt32) + 8 = 1048568 by decide] with HspillPtr
    wasm_twp_bind Wasm.SmallStep.twp_load32 ptr
      (by decide) (by decide) (by decide) (by decide) with HspillPtr' => HspillPtr
    wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_call «module» 0 func0Def
      (by simp [«module»]) (by simp [«module»]) with Hruntime
    simp [func0Def, Function.toLocals, Function.numParams]
    iapply twp_func0_alias_context_smallStep_wp
      (iprop% pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len)
      ptr len i oldScratch oldValue hi hroom _
    · iintro ⟨⟨HspillPtr, HspillLen⟩,
        Hruntime, Hglobal, Hscratch, Hcell⟩
      wasm_twp_return_from_call Hruntime [List.take, List.nil_append]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      wasm_twp_rebind Wasm.SmallStep.twp_globalSet with Hglobal
      rw [show (16 : UInt32) + 1048560 = 1048576 by decide]
      rw [show (3 % 32 : UInt32) = 3 by decide]
      iapply Wasm.SmallStep.twp_returnFromFunction
      simp only [List.take, List.nil_append]
      iapply twp.value rfl
      isplitr_pureexact rfl
      · iframe
    · rw [show (3 % 32 : UInt32) = 3 by decide]
      iframe
  · rw [show (3 % 32 : UInt32) = 3 by decide]
    iframe

/-! ## Parameterized authoritative export contract -/

def func4ConfigFromStore (wasm : Store Unit)
    (ptr len i j : UInt32) : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 ptr, .i32 len, .i32 i, .i32 j],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := wasm } }

/-- Fully parameterized distinct-address partial correctness. The footprint
decomposition is the separation-logic form of disjointness: it is impossible
to supply two exclusive `u64` owners for overlapping bytes. -/
theorem func4_distinct_store_partiallyMeets
    (wasm : Store Unit) (ptr len i j : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ (storeResolve (func4ConfigFromStore wasm ptr len i j).store))
    (hinBounds : heapAddressesInBounds σ (storeResolve (func4ConfigFromStore wasm ptr len i j).store))
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB)
    (hglobalOwn : ∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) :
    Wasm.SmallStep.PartiallyMeets
      (func4ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldB ∧
          store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr) = oldA) := by
  let addressI := (i <<< (3 % 32)) + ptr
  let addressJ := (j <<< (3 % 32)) + ptr
  have hroomI' : addressI.toNat + 8 ≤ 4294967296 := by simpa [addressI] using hroomI
  have hroomJ' : addressJ.toNat + 8 ≤ 4294967296 := by simpa [addressJ] using hroomJ
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6, hi7⟩ := UInt32.addSteps8 addressI hroomI'
  obtain ⟨hj1, hj2, hj3, hj4, hj5, hj6, hj7⟩ := UInt32.addSteps8 addressJ hroomJ'
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · simp only [func4ConfigFromStore]; decide
  · intro gs
    simp only [func4ConfigFromStore, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime, _Henv⟩
    ihave Hresources := hresources $$ Hheap
    ihave Hglobal := hglobalOwn $$ Hglobals
    icases Hresources with
      ⟨Hscratch, HspillPtr, HspillLen, HA, HB⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 oldA ∗
          pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
          pointsTo_u64 0 addressI oldB ∗ pointsTo_u64 0 addressJ oldA) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 addressI = oldB ∧
            store.wasm.mem.read64 addressJ = oldA⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, HA, HB⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts_frame
        store 0 [] 0 addressI oldB hi1 hi2 hi3 hi4 hi5 hi6 hi7 $$
          [$Hstate $HA] with ⟨Hstate, _HA, %HfactsI⟩
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 addressJ oldA hj1 hj2 hj3 hj4 hj5 hj6 hj7 $$
          [$Hstate $HB] with %HfactsJ
      ipureexact ⟨hvalues, HfactsI.1, HfactsJ.1⟩
    iapply wp_mono hpost
    iapply func4_happy_smallStep_wp
      ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
      hi hj hroomI hroomJ
    iframe

/-- Fully parameterized equal-index partial correctness.  This version needs
only one exclusive array-word owner and proves that the reached physical word
is unchanged. -/
theorem func4_alias_store_partiallyMeets
    (wasm : Store Unit) (ptr len i : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ (storeResolve (func4ConfigFromStore wasm ptr len i i).store))
    (hinBounds : heapAddressesInBounds σ (storeResolve (func4ConfigFromStore wasm ptr len i i).store))
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue)
    (hglobalOwn : ∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) :
    Wasm.SmallStep.PartiallyMeets
      (func4ConfigFromStore wasm ptr len i i)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldValue) := by
  let address := (i <<< (3 % 32)) + ptr
  have hroom' : address.toNat + 8 ≤ 4294967296 := by simpa [address] using hroom
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 address hroom'
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · simp only [func4ConfigFromStore]; decide
  · intro gs
    simp only [func4ConfigFromStore, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime, _Henv⟩
    ihave Hresources := hresources $$ Hheap
    ihave Hglobal := hglobalOwn $$ Hglobals
    icases Hresources with
      ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 oldValue ∗
          pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
          pointsTo_u64 0 address oldValue) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read64 address = oldValue⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, Hcell⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 address oldValue h1 h2 h3 h4 h5 h6 h7 $$
          [$Hstate $Hcell] with %Hfacts
      ipureexact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    iapply func4_alias_smallStep_wp
      ptr len i oldSpillPtr oldSpillLen oldScratch oldValue hi hroom
    iframe

theorem func4_distinct_store_terminatesWith
    (wasm : Store Unit) (ptr len i j : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldA oldB : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len) (hj : j < len)
    (hroomI : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hroomJ : ((j <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ
      (storeResolve (func4ConfigFromStore wasm ptr len i j).store))
    (hinBounds : heapAddressesInBounds σ
      (storeResolve (func4ConfigFromStore wasm ptr len i j).store))
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldA ∗
      pointsTo_u64 0 ((j <<< (3 % 32)) + ptr) oldB)
    (hglobalOwn : ∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) :
    Wasm.SmallStep.TerminatesWith
      (func4ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldB ∧
          store.wasm.mem.read64 ((j <<< (3 % 32)) + ptr) = oldA) := by
  let addressI := (i <<< (3 % 32)) + ptr
  let addressJ := (j <<< (3 % 32)) + ptr
  have hroomI' : addressI.toNat + 8 ≤ 4294967296 := by simpa [addressI] using hroomI
  have hroomJ' : addressJ.toNat + 8 ≤ 4294967296 := by simpa [addressJ] using hroomJ
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6, hi7⟩ := UInt32.addSteps8 addressI hroomI'
  obtain ⟨hj1, hj2, hj3, hj4, hj5, hj6, hj7⟩ := UInt32.addSteps8 addressJ hroomJ'
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_terminates
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · simp only [func4ConfigFromStore]; decide
  · intro _hlc _gs
    simp only [func4ConfigFromStore, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hresources := hresources $$ Hheap
    ihave Hglobal := hglobalOwn $$ Hglobals
    icases Hresources with
      ⟨Hscratch, HspillPtr, HspillLen, HA, HB⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 oldA ∗
          pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
          pointsTo_u64 0 addressI oldB ∗ pointsTo_u64 0 addressJ oldA) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 addressI = oldB ∧
            store.wasm.mem.read64 addressJ = oldA⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, HA, HB⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts_frame
        store 0 [] 0 addressI oldB hi1 hi2 hi3 hi4 hi5 hi6 hi7 $$
          [$Hstate $HA] with ⟨Hstate, _HA, %HfactsI⟩
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 addressJ oldA hj1 hj2 hj3 hj4 hj5 hj6 hj7 $$
          [$Hstate $HB] with %HfactsJ
      ipureexact ⟨hvalues, HfactsI.1, HfactsJ.1⟩
    iapply twp.mono hpost
    iapply twp_func4_happy_smallStep_wp
      ptr len i j oldSpillPtr oldSpillLen oldScratch oldA oldB
      hi hj hroomI hroomJ
    iframe

theorem func4_alias_store_terminatesWith
    (wasm : Store Unit) (ptr len i : UInt32)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch oldValue : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hi : i < len)
    (hroom : ((i <<< (3 % 32)) + ptr).toNat + 8 ≤ 4294967296)
    (hagree : heapAgreesWithMem σ
      (storeResolve (func4ConfigFromStore wasm ptr len i i).store))
    (hinBounds : heapAddressesInBounds σ
      (storeResolve (func4ConfigFromStore wasm ptr len i i).store))
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      pointsTo_u64 0 ((i <<< (3 % 32)) + ptr) oldValue)
    (hglobalOwn : ∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) :
    Wasm.SmallStep.TerminatesWith
      (func4ConfigFromStore wasm ptr len i i)
      (fun values store =>
        values = [] ∧
          store.wasm.mem.read64 ((i <<< (3 % 32)) + ptr) = oldValue) := by
  let address := (i <<< (3 % 32)) + ptr
  have hroom' : address.toNat + 8 ≤ 4294967296 := by simpa [address] using hroom
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := UInt32.addSteps8 address hroom'
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_terminates
      (α := Unit) (σ := σ) (globalσ := globalσ)
  · exact hagree
  · exact hinBounds
  · exact hglobals
  · simp only [func4ConfigFromStore]; decide
  · intro _hlc _gs
    simp only [func4ConfigFromStore, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave Hresources := hresources $$ Hheap
    ihave Hglobal := hglobalOwn $$ Hglobals
    icases Hresources with
      ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 oldValue ∗
          pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
          pointsTo_u64 0 address oldValue) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧
            store.wasm.mem.read64 address = oldValue⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, Hcell⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 address oldValue h1 h2 h3 h4 h5 h6 h7 $$
          [$Hstate $Hcell] with %Hfacts
      ipureexact ⟨hvalues, Hfacts.1⟩
    iapply twp.mono hpost
    iapply twp_func4_alias_smallStep_wp
      ptr len i oldSpillPtr oldSpillLen oldScratch oldValue hi hroom
    iframe

/-- Whole-array authoritative swap contract.  Like `func4_distinct_store_terminatesWith`
but takes `array64At 0 ptr xs` as a single resource instead of two individual cells,
and states the postcondition as a `Mem.readWords64` list equation. Covers both the
`i ≠ j` and `i = j` cases internally. -/
theorem func4_store_terminatesWith_array
    (wasm : Store Unit) (ptr len i j : UInt32)
    (xs : List UInt64)
    (oldSpillPtr oldSpillLen : UInt32)
    (oldScratch : UInt64)
    (σ : WasmHeapMap (Option UInt8))
    (globalσ : WasmGlobalMap Value)
    (hlen : xs.length = len.toNat)
    (hi : i < len) (hj : j < len)
    (hroom : ptr.toNat + 8 * xs.length < UInt32.size)
    (hagree : heapAgreesWithMem σ
      (storeResolve (func4ConfigFromStore wasm ptr len i j).store))
    (hinBounds : heapAddressesInBounds σ
      (storeResolve (func4ConfigFromStore wasm ptr len i j).store))
    (hglobals : globalHeapAgrees globalσ wasm.globals)
    (hresources : ∀ [WasmHeapGS Unit],
      ([∗map] address ↦ value ∈ σ,
        pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
          address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 oldScratch ∗
      pointsTo_u32 0 1048568 oldSpillPtr ∗
      pointsTo_u32 0 1048572 oldSpillLen ∗
      array64At 0 ptr xs)
    (hglobalOwn : ∀ [WasmGlobalGS Unit],
      ([∗map] index ↦ value ∈ globalσ,
        globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576)) :
    Wasm.SmallStep.TerminatesWith
      (func4ConfigFromStore wasm ptr len i j)
      (fun values store =>
        values = [] ∧
          Mem.readWords64 store.wasm.mem ptr xs.length =
            (xs.set i.toNat (xs.getD j.toNat 0)).set j.toNat (xs.getD i.toNat 0)) := by
  have hi' : i.toNat < xs.length := by rw [hlen]; exact_mod_cast hi
  have hj' : j.toNat < xs.length := by rw [hlen]; exact_mod_cast hj
  -- Bridge: array64At uses `ptr + 8 * UInt32.ofNat k` addresses;
  -- the WP rules use `(k <<< (3 % 32)) + ptr` addresses.
  have haddrI : ptr + 8 * i = (i <<< (3 % 32 : UInt32)) + ptr :=
    (Project.SwapElements.Spec.elemAddr_of_shl ptr i).symm
  have haddrJ : ptr + 8 * j = (j <<< (3 % 32 : UInt32)) + ptr :=
    (Project.SwapElements.Spec.elemAddr_of_shl ptr j).symm
  have haddr_toNat_I : ((i <<< (3 % 32 : UInt32)) + ptr).toNat = ptr.toNat + 8 * i.toNat := by
    rw [Project.SwapElements.Spec.elemAddr_of_shl]
    exact Project.SwapElements.Spec.elemAddr_toNat ptr i (by simp only [UInt32.size] at hroom; omega)
  have haddr_toNat_J : ((j <<< (3 % 32 : UInt32)) + ptr).toNat = ptr.toNat + 8 * j.toNat := by
    rw [Project.SwapElements.Spec.elemAddr_of_shl]
    exact Project.SwapElements.Spec.elemAddr_toNat ptr j (by simp only [UInt32.size] at hroom; omega)
  have hroomI : ((i <<< (3 % 32 : UInt32)) + ptr).toNat + 8 ≤ 4294967296 := by
    rw [haddr_toNat_I]; simp only [UInt32.size] at hroom; omega
  have hroomJ : ((j <<< (3 % 32 : UInt32)) + ptr).toNat + 8 ≤ 4294967296 := by
    rw [haddr_toNat_J]; simp only [UInt32.size] at hroom; omega
  by_cases hij : i = j
  · subst hij
    apply wasm_smallStep_heap_globals_runtime_store_terminates
      (α := Unit) (σ := σ) (globalσ := globalσ)
    · exact hagree
    · exact hinBounds
    · exact hglobals
    · simp only [func4ConfigFromStore]; decide
    · intro _hlc _gs
      simp only [func4ConfigFromStore, RuntimeEnv.currentModule_mk1]
      iintro ⟨Hheap, Hglobals, Hruntime⟩
      ihave Hresources := hresources $$ Hheap
      ihave Hglobal := hglobalOwn $$ Hglobals
      icases Hresources with ⟨Hscratch, HspillPtr, HspillLen, Harray⟩
      ihave ⟨Hcell, Hback⟩ := array64At_get 0 ptr xs i.toNat hi' $$ Harray
      ihave Hcell' : pointsTo_u64 0 ((i <<< (3 % 32 : UInt32)) + ptr) xs[i.toNat] $$ [Hcell]
      · irw_exact [show ptr + 8 * UInt32.ofNat i.toNat = (i <<< (3 % 32 : UInt32)) + ptr from
            by rw [UInt32.ofNat_toNat]; exact haddrI] with Hcell
      have hpost : ∀ values : List Value,
          (iprop% (pointsTo_u64 0 (ptr + 8 * UInt32.ofNat i.toNat) xs[i.toNat] -∗
              array64At 0 ptr xs) ∗
            ⌜values = []⌝ ∗
            globalPointsToAt 0 0 (.i32 1048576) ∗
            pointsTo_u64 0 1048552 xs[i.toNat] ∗
            pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
            pointsTo_u64 0 ((i <<< (3 % 32 : UInt32)) + ptr) xs[i.toNat]) ⊢
          (iprop% ∀ (store : MachineStore Unit)
              (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
            ⌜values = [] ∧
              Mem.readWords64 store.wasm.mem ptr xs.length =
                (xs.set i.toNat (xs.getD i.toNat 0)).set i.toNat (xs.getD i.toNat 0)⌝) := by
        intro values
        iintro ⟨Hback_after, %hvalues, _Hglobal, _Hscratch, _HspillPtr, _HspillLen,
            Hcell_after⟩
          %store %_observations Hstate
        ihave Hcell_conv : pointsTo_u64 0 (ptr + 8 * UInt32.ofNat i.toNat) xs[i.toNat] $$ [Hcell_after]
        · irw_exact [show ptr + 8 * UInt32.ofNat i.toNat = (i <<< (3 % 32 : UInt32)) + ptr from
              by rw [UInt32.ofNat_toNat]; exact haddrI] with Hcell_after
        ihave Harray_restored := Hback_after $$ Hcell_conv
        imod array64At_words store 0 [] 0 ptr xs hroom $$
          [$Hstate $Harray_restored] with ⟨_Hstate, _Harray, %hread⟩
        have heq : (xs.set i.toNat (xs.getD i.toNat 0)).set i.toNat (xs.getD i.toNat 0) = xs :=
          by simp [List.getD, hi', List.set_getElem_self]
        ipureexact ⟨hvalues, hread.trans heq.symm⟩
      iapply twp.mono hpost
      iapply (twp.frame_l (R := iprop%
          (pointsTo_u64 0 (ptr + 8 * UInt32.ofNat i.toNat) xs[i.toNat] -∗ array64At 0 ptr xs)))
      isplitl [Hback]
      · iexact Hback
      · iapply twp_func4_alias_smallStep_wp
            ptr len i oldSpillPtr oldSpillLen oldScratch xs[i.toNat] hi hroomI
        iframe
  · have hij' : i.toNat ≠ j.toNat := fun h => hij (UInt32.toNat_inj.mp h)
    apply wasm_smallStep_heap_globals_runtime_store_terminates
      (α := Unit) (σ := σ) (globalσ := globalσ)
    · exact hagree
    · exact hinBounds
    · exact hglobals
    · simp only [func4ConfigFromStore]; decide
    · intro _hlc _gs
      simp only [func4ConfigFromStore, RuntimeEnv.currentModule_mk1]
      iintro ⟨Hheap, Hglobals, Hruntime⟩
      ihave Hresources := hresources $$ Hheap
      ihave Hglobal := hglobalOwn $$ Hglobals
      icases Hresources with ⟨Hscratch, HspillPtr, HspillLen, Harray⟩
      ihave ⟨HA, HB, Hback⟩ :=
        array64At_swap_focus 0 ptr xs i.toNat j.toNat hi' hj' hij' $$ Harray
      ihave HA' : pointsTo_u64 0 ((i <<< (3 % 32 : UInt32)) + ptr) xs[i.toNat] $$ [HA]
      · irw_exact [show ptr + 8 * UInt32.ofNat i.toNat = (i <<< (3 % 32 : UInt32)) + ptr from
            by rw [UInt32.ofNat_toNat]; exact haddrI] with HA
      ihave HB' : pointsTo_u64 0 ((j <<< (3 % 32 : UInt32)) + ptr) xs[j.toNat] $$ [HB]
      · irw_exact [show ptr + 8 * UInt32.ofNat j.toNat = (j <<< (3 % 32 : UInt32)) + ptr from
            by rw [UInt32.ofNat_toNat]; exact haddrJ] with HB
      ispecialize Hback $$ %xs[j.toNat] %xs[i.toNat]
      have hpost : ∀ values : List Value,
          (iprop% (pointsTo_u64 0 ((i <<< (3 % 32 : UInt32)) + ptr) xs[j.toNat] ∗
              pointsTo_u64 0 ((j <<< (3 % 32 : UInt32)) + ptr) xs[i.toNat] -∗
              array64At 0 ptr (xs.set i.toNat xs[j.toNat] |>.set j.toNat xs[i.toNat])) ∗
            ⌜values = []⌝ ∗
            globalPointsToAt 0 0 (.i32 1048576) ∗
            pointsTo_u64 0 1048552 xs[i.toNat] ∗
            pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len ∗
            pointsTo_u64 0 ((i <<< (3 % 32 : UInt32)) + ptr) xs[j.toNat] ∗
            pointsTo_u64 0 ((j <<< (3 % 32 : UInt32)) + ptr) xs[i.toNat]) ⊢
          (iprop% ∀ (store : MachineStore Unit)
              (_observations : List StepKind),
            stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
            ⌜values = [] ∧
              Mem.readWords64 store.wasm.mem ptr xs.length =
                (xs.set i.toNat (xs.getD j.toNat 0)).set j.toNat (xs.getD i.toNat 0)⌝) := by
        intro values
        iintro ⟨Hback_after, %hvalues, _Hglobal, _Hscratch, _HspillPtr, _HspillLen,
            HA_after, HB_after⟩
          %store %_observations Hstate
        ihave Harray_restored := Hback_after $$ [HA_after HB_after]
        · iframe
        have hfit' : ptr.toNat + 8 *
            (xs.set i.toNat xs[j.toNat] |>.set j.toNat xs[i.toNat]).length < UInt32.size :=
          by simp only [List.length_set]; exact hroom
        imod array64At_words store 0 [] 0 ptr
            (xs.set i.toNat xs[j.toNat] |>.set j.toNat xs[i.toNat]) hfit' $$
          [$Hstate $Harray_restored] with ⟨_Hstate, _Harray, %hread⟩
        ipureexact ⟨hvalues, by
          simp only [List.length_set] at hread
          simp only [show xs[j.toNat] = xs.getD j.toNat 0 from by simp [List.getD, hj'],
                     show xs[i.toNat] = xs.getD i.toNat 0 from by simp [List.getD, hi']] at hread
          exact hread⟩
      iapply twp.mono hpost
      iapply (twp.frame_l (R := iprop%
          (pointsTo_u64 0 ((i <<< (3 % 32 : UInt32)) + ptr) xs[j.toNat] ∗
           pointsTo_u64 0 ((j <<< (3 % 32 : UInt32)) + ptr) xs[i.toNat] -∗
           array64At 0 ptr (xs.set i.toNat xs[j.toNat] |>.set j.toNat xs[i.toNat]))))
      isplitl [Hback]
      · irw_exact [show (i <<< (3 % 32 : UInt32)) + ptr = ptr + 8 * UInt32.ofNat i.toNat from
            by rw [UInt32.ofNat_toNat]; exact haddrI.symm,
          show (j <<< (3 % 32 : UInt32)) + ptr = ptr + 8 * UInt32.ofNat j.toNat from
            by rw [UInt32.ofNat_toNat]; exact haddrJ.symm] with Hback
      · iapply twp_func4_happy_smallStep_wp
            ptr len i j oldSpillPtr oldSpillLen oldScratch xs[i.toNat] xs[j.toNat]
            hi hj hroomI hroomJ
        iframe

/-! ## Closed authoritative small-step execution of the spill helper -/


def func3Config (ptr len : UInt32) : Wasm.SmallStep.Config Unit :=
  { expr := .running
      ⟨⟨[.i32 1048568, .i32 ptr, .i32 len, .i32 1048652], [], []⟩,
        func3, 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := «module».initialStore } }

def func3Heap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap ∅ 0 1048568 0) 0 1048572 0

theorem func3Heap_agrees (ptr len : UInt32) :
    heapAgreesWithMem func3Heap (storeResolve (func3Config ptr len).store) := by
  let mem := («module».initialStore : Store Unit).mem
  let resolve := storeResolve (func3Config ptr len).store
  have hresolve : resolve 0 = some mem := rfl
  unfold func3Heap
  apply_insert_physical_word32_sound hresolve
  · apply_insert_physical_word32_sound hresolve
    · exact heapAgreesWithMem_empty _
    · decide
  · decide

theorem func3Heap_inBounds (ptr len : UInt32) :
    heapAddressesInBounds func3Heap
      (storeResolve (func3Config ptr len).store) := by
  let mem := («module».initialStore : Store Unit).mem
  let resolve := storeResolve (func3Config ptr len).store
  have hresolve : resolve 0 = some mem := rfl
  unfold func3Heap
  apply_insert_physical_word32_inBounds hresolve
  · apply_insert_physical_word32_inBounds hresolve
    · exact heapAddressesInBounds_empty _
    · decide
    · decide
  · decide
  · decide

theorem func3Heap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func3Heap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 0 := by
  unfold func3Heap
  iintro Hheap
  ihave ⟨Hlen, Hheap⟩ := store32Heap_pointsTo
    (store32Heap ∅ 0 1048568 0) 0 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hptr, Hempty⟩ := store32Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048568 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  iframe

/-- The spill helper's existing instruction proof, closed through iris-lean
adequacy and the authoritative physical byte interpretation. -/
theorem func3_smallStep (ptr len : UInt32) :
    Wasm.SmallStep.PartiallyMeets (func3Config ptr len)
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.adequate_to_partiallyMeets
  apply Wasm.SmallStep.wasm_smallStep_heap_adequacy
    (α := Unit) (σ := func3Heap)
    (φ := fun values => values = [])
  · exact func3Heap_agrees ptr len
  · exact func3Heap_inBounds ptr len
  · intro gs
    iintro Hheap
    ihave ⟨Hptr, Hlen⟩ := func3Heap_pointsTo $$ Hheap
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          pointsTo_u32 0 1048568 ptr ∗ pointsTo_u32 0 1048572 len) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hptr, _Hlen⟩
      ipureexact hvalues
    iapply wp_mono hpost
    simp only [func3Config]
    iapply func3_smallStep_wp (s := Stuckness.NotStuck) (E := ⊤)
      0 0 ptr len
    iframe

/-! ## Closed exported two-element example -/

def func4ExampleHeap : WasmHeapMap (Option UInt8) :=
  store64Heap
    (store64Heap
      (store32Heap
        (store32Heap (store64Heap ∅ 0 1048552 0) 0 1048568 0)
        0 1048572 0)
      0 0 11)
    0 8 22

private def func4ExampleMem (memory : Mem) : Mem :=
  ((((memory.write64 1048552 0).write32 1048568 0).write32 1048572 0
    ).write64 0 11).write64 8 22

def func4ExampleConfig : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 0, .i32 2, .i32 0, .i32 1],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := func4ExampleMem initial.mem } } }

def func4ExampleGlobals : WasmGlobalMap Value :=
  insert ∅ ⟨0, 0⟩ (.i32 1048576)

theorem func4ExampleHeap_agrees :
    heapAgreesWithMem func4ExampleHeap
      (storeResolve func4ExampleConfig.store) := by
  unfold func4ExampleHeap
  apply_insert_physical_word64_sound rfl
  · apply_insert_physical_word64_sound rfl
    · apply_insert_physical_word32_sound rfl
      · apply_insert_physical_word32_sound rfl
        · apply_insert_physical_word64_sound rfl
          · exact heapAgreesWithMem_empty _
          · decide +kernel
        · decide +kernel
      · decide +kernel
    · decide +kernel
  · decide +kernel

theorem func4ExampleHeap_inBounds :
    heapAddressesInBounds func4ExampleHeap
      (storeResolve func4ExampleConfig.store) := by
  unfold func4ExampleHeap
  apply_insert_physical_word64_inBounds rfl
  · apply_insert_physical_word64_inBounds rfl
    · apply_insert_physical_word32_inBounds rfl
      · apply_insert_physical_word32_inBounds rfl
        · apply_insert_physical_word64_inBounds rfl
          · exact heapAddressesInBounds_empty _
          · decide +kernel
        · decide +kernel
        · decide +kernel
      · decide +kernel
      · decide +kernel
    · decide +kernel
  · decide +kernel

theorem func4ExampleGlobals_agree :
    globalHeapAgrees func4ExampleGlobals
      func4ExampleConfig.store.wasm.globals := globalHeapAgrees_singleton rfl

theorem func4ExampleHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func4ExampleHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 0 ∗
      pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 0 ∗
      pointsTo_u64 0 0 11 ∗ pointsTo_u64 0 8 22 := by
  unfold func4ExampleHeap
  iintro Hheap
  ihave ⟨H8, Hheap⟩ := store64Heap_pointsTo _ 0 8 22
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨H0, Hheap⟩ := store64Heap_pointsTo _ 0 0 11
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hlen, Hheap⟩ := store32Heap_pointsTo _ 0 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hptr, Hheap⟩ := store32Heap_pointsTo _ 0 1048568 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hscratch, Hempty⟩ := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  iframe

theorem func4ExampleGlobals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ func4ExampleGlobals,
      globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048576) := by
  unfold func4ExampleGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  simp only [globalPointsToAt_eq]; rfl

/-- The real exported swap executes under the authoritative small-step
semantics on a concrete two-element array and returns normally. -/
theorem func4Example_smallStep :
    Wasm.SmallStep.PartiallyMeets func4ExampleConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets
    (α := Unit) (σ := func4ExampleHeap)
    (globalσ := func4ExampleGlobals)
    (φ := fun values => values = [])
  · exact func4ExampleHeap_agrees
  · exact func4ExampleHeap_inBounds
  · exact func4ExampleGlobals_agree
  wasm_adequacy_intro gs =>
    simp only [func4ExampleConfig, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave ⟨Hscratch, HspillPtr, HspillLen, H0, H8⟩ := func4ExampleHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 11 ∗
          pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 2 ∗
          pointsTo_u64 0 0 22 ∗ pointsTo_u64 0 8 11) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hresources⟩
      ipureexact hvalues
    iapply wp_mono hpost
    have hfunc4 := func4_happy_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 2 0 1 0 0 0 11 22
      (by decide) (by decide) (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide,
      show ((1 : UInt32) <<< (3 % 32)) + 0 = 8 by decide] at hfunc4
    iapply_frame hfunc4

/-- State-sensitive adequacy for the distinct-index export example proves
both sides of the physical swap in the reached `MachineStore`. -/
theorem func4Example_store_smallStep :
    Wasm.SmallStep.PartiallyMeets func4ExampleConfig
      (fun values store =>
        values = [] ∧ store.wasm.mem.read64 0 = 22 ∧
          store.wasm.mem.read64 8 = 11) := by
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets
      (α := Unit) (σ := func4ExampleHeap)
      (globalσ := func4ExampleGlobals)
  · exact func4ExampleHeap_agrees
  · exact func4ExampleHeap_inBounds
  · exact func4ExampleGlobals_agree
  wasm_adequacy_intro gs =>
    simp only [func4ExampleConfig, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime, _Henv⟩
    ihave ⟨Hscratch, HspillPtr, HspillLen, H0, H8⟩ := func4ExampleHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 11 ∗
          pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 2 ∗
          pointsTo_u64 0 0 22 ∗ pointsTo_u64 0 8 11) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 0 = 22 ∧
            store.wasm.mem.read64 8 = 11⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, H0, H8⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts_frame
        store 0 [] 0 0 22
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $H0] with ⟨Hstate, _H0, %Hfacts0⟩
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 8 11
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $H8] with %Hfacts8
      ipureexact ⟨hvalues, Hfacts0.1, Hfacts8.1⟩
    iapply wp_mono hpost
    have hfunc4 := func4_happy_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 2 0 1 0 0 0 11 22
      (by decide) (by decide) (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide,
      show ((1 : UInt32) <<< (3 % 32)) + 0 = 8 by decide] at hfunc4
    iapply_frame hfunc4

/-- Executable finite-trace witness complementing the Iris partial-correctness
proof for the distinct-index export example. -/
theorem func4Example_terminates :
    Wasm.SmallStep.TerminatesWith func4ExampleConfig
      (fun values _store => values = []) :=
  Wasm.SmallStep.runSteps_values_terminates (fuel := 200) (by decide +kernel)

def func4AliasHeap : WasmHeapMap (Option UInt8) :=
  store64Heap
    (store32Heap
      (store32Heap (store64Heap ∅ 0 1048552 0) 0 1048568 0)
      0 1048572 0)
    0 0 42

private def func4AliasMem (memory : Mem) : Mem :=
  (((memory.write64 1048552 0).write32 1048568 0).write32 1048572 0
    ).write64 0 42

def func4AliasConfig : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 0, .i32 1, .i32 0, .i32 0],
          [.i32 0, .i32 0, .i32 0], []⟩,
        func4, 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm := { initial with mem := func4AliasMem initial.mem } } }

theorem func4AliasHeap_agrees :
    heapAgreesWithMem func4AliasHeap
      (storeResolve func4AliasConfig.store) := by
  unfold func4AliasHeap
  apply_insert_physical_word64_sound rfl
  · apply_insert_physical_word32_sound rfl
    · apply_insert_physical_word32_sound rfl
      · apply_insert_physical_word64_sound rfl
        · exact heapAgreesWithMem_empty _
        · decide +kernel
      · decide +kernel
    · decide +kernel
  · decide +kernel

theorem func4AliasHeap_inBounds :
    heapAddressesInBounds func4AliasHeap
      (storeResolve func4AliasConfig.store) := by
  unfold func4AliasHeap
  apply_insert_physical_word64_inBounds rfl
  · apply_insert_physical_word32_inBounds rfl
    · apply_insert_physical_word32_inBounds rfl
      · apply_insert_physical_word64_inBounds rfl
        · exact heapAddressesInBounds_empty _
        · decide +kernel
      · decide +kernel
      · decide +kernel
    · decide +kernel
    · decide +kernel
  · decide +kernel

theorem func4AliasHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func4AliasHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 0 ∗
      pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 0 ∗
      pointsTo_u64 0 0 42 := by
  unfold func4AliasHeap
  iintro Hheap
  ihave ⟨Hcell, Hheap⟩ := store64Heap_pointsTo _ 0 0 42
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hlen, Hheap⟩ := store32Heap_pointsTo _ 0 1048572 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hptr, Hheap⟩ := store32Heap_pointsTo _ 0 1048568 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hscratch, Hempty⟩ := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  iframe

/-- The exported wrapper also closes in the equal-index case from one array
word of authoritative ownership. -/
theorem func4Alias_smallStep :
    Wasm.SmallStep.PartiallyMeets func4AliasConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets
    (α := Unit) (σ := func4AliasHeap)
    (globalσ := func4ExampleGlobals)
    (φ := fun values => values = [])
  · exact func4AliasHeap_agrees
  · exact func4AliasHeap_inBounds
  · exact func4ExampleGlobals_agree
  wasm_adequacy_intro gs =>
    simp only [func4AliasConfig, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩ := func4AliasHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 42 ∗
          pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 1 ∗
          pointsTo_u64 0 0 42) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hresources⟩
      ipureexact hvalues
    iapply wp_mono hpost
    have halias := func4_alias_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 1 0 0 0 0 42 (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide] at halias
    iapply_frame halias

/-- State-sensitive adequacy for the exported equal-index case: the physical
array word in the reached `MachineStore` is unchanged. -/
theorem func4Alias_store_smallStep :
    Wasm.SmallStep.PartiallyMeets func4AliasConfig
      (fun values store =>
        values = [] ∧ store.wasm.mem.read64 0 = 42) := by
  apply
    Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_store_partiallyMeets
      (α := Unit) (σ := func4AliasHeap)
      (globalσ := func4ExampleGlobals)
  · exact func4AliasHeap_agrees
  · exact func4AliasHeap_inBounds
  · exact func4ExampleGlobals_agree
  wasm_adequacy_intro gs =>
    simp only [func4AliasConfig, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime, _Henv⟩
    ihave ⟨Hscratch, HspillPtr, HspillLen, Hcell⟩ := func4AliasHeap_pointsTo $$ Hheap
    ihave Hglobal := func4ExampleGlobals_pointsTo $$ Hglobals
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048576) ∗
          pointsTo_u64 0 1048552 42 ∗
          pointsTo_u32 0 1048568 0 ∗ pointsTo_u32 0 1048572 1 ∗
          pointsTo_u64 0 0 42) ⊢
        (iprop% ∀ (store : Wasm.SmallStep.MachineStore Unit)
            (_observations : List Wasm.SmallStep.StepKind),
          stateInterp (GF := WasmHeapGF Unit) store 0 [] 0 -∗
          ⌜values = [] ∧ store.wasm.mem.read64 0 = 42⌝) := by
      intro values
      iintro ⟨%hvalues, _Hglobal, _Hscratch,
        _HspillPtr, _HspillLen, Hcell⟩
        %store %_observations Hstate
      imod Wasm.SmallStep.stateInterp_pointsTo_u64_facts
        store 0 [] 0 0 42
        (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) $$
          [$Hstate $Hcell] with %Hfacts
      ipureexact ⟨hvalues, Hfacts.1⟩
    iapply wp_mono hpost
    have halias := func4_alias_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 1 0 0 0 0 42 (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide] at halias
    iapply_frame halias

/-- Executable finite-trace witness for the equal-index export example. -/
theorem func4Alias_terminates :
    Wasm.SmallStep.TerminatesWith func4AliasConfig
      (fun values _store => values = []) :=
  Wasm.SmallStep.runSteps_values_terminates (fuel := 200) (by decide +kernel)

/-! ## Closed equal-index example -/

def func0AliasHeap : WasmHeapMap (Option UInt8) :=
  store64Heap (store64Heap ∅ 0 1048552 0) 0 0 42

def func0AliasConfig : Wasm.SmallStep.Config Unit :=
  let initial : Store Unit := «module».initialStore
  { expr := .running
      ⟨⟨[.i32 0, .i32 1, .i32 0, .i32 0], [], []⟩,
        func0, 0, [], [], []⟩
    store :=
      { runtime := { instances := #[{ module := «module», host := {} }], entry := ⟨0⟩ }
        wasm :=
          { initial with
            mem := (initial.mem.write64 1048552 0).write64 0 42
            globals := { globals := [Value.i32 1048560] } } } }

def func0AliasGlobals : WasmGlobalMap Value :=
  insert ∅ ⟨0, 0⟩ (.i32 1048560)

theorem func0AliasHeap_agrees :
    heapAgreesWithMem func0AliasHeap
      (storeResolve func0AliasConfig.store) := by
  unfold func0AliasHeap
  apply_insert_physical_word64_sound rfl
  · apply_insert_physical_word64_sound rfl
    · exact heapAgreesWithMem_empty _
    · decide +kernel
  · decide +kernel

theorem func0AliasHeap_inBounds :
    heapAddressesInBounds func0AliasHeap
      (storeResolve func0AliasConfig.store) := by
  unfold func0AliasHeap
  apply_insert_physical_word64_inBounds rfl
  · apply_insert_physical_word64_inBounds rfl
    · exact heapAddressesInBounds_empty _
    · decide +kernel
  · decide +kernel

theorem func0AliasGlobals_agree :
    globalHeapAgrees func0AliasGlobals
      func0AliasConfig.store.wasm.globals := globalHeapAgrees_singleton rfl

theorem func0AliasHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func0AliasHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 0 ∗ pointsTo_u64 0 0 42 := by
  unfold func0AliasHeap
  iintro Hheap
  ihave ⟨Hcell, Hheap⟩ := store64Heap_pointsTo _ 0 0 42
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hscratch, Hempty⟩ := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048552 0
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  iframe

theorem func0AliasGlobals_pointsTo [WasmGlobalGS Unit] :
    ([∗map] index ↦ value ∈ func0AliasGlobals,
      globalPointsTo index value) ⊢
      globalPointsToAt 0 0 (.i32 1048560) := by
  unfold func0AliasGlobals
  rw [(BI.BigSepM.bigSepM_insert (get?_empty (⟨0, 0⟩ : GlobalKey))).to_eq,
    BI.BigSepM.bigSepM_empty.to_eq, BI.sep_emp.to_eq]
  simp only [globalPointsToAt_eq]; rfl

/-- Same-index swapping is a real one-cell execution, not a degenerate proof
that duplicates exclusive ownership. -/
theorem func0Alias_smallStep :
    Wasm.SmallStep.PartiallyMeets func0AliasConfig
      (fun values _store => values = []) := by
  apply Wasm.SmallStep.wasm_smallStep_heap_globals_runtime_partiallyMeets
    (α := Unit) (σ := func0AliasHeap)
    (globalσ := func0AliasGlobals)
    (φ := fun values => values = [])
  · exact func0AliasHeap_agrees
  · exact func0AliasHeap_inBounds
  · exact func0AliasGlobals_agree
  wasm_adequacy_intro gs =>
    simp only [func0AliasConfig, Wasm.SmallStep.RuntimeEnv.currentModule_mk1]
    iintro ⟨Hheap, Hglobals, Hruntime⟩
    ihave ⟨Hscratch, Hcell⟩ := func0AliasHeap_pointsTo $$ Hheap
    ihave Hglobal := func0AliasGlobals_pointsTo $$ Hglobals
    have hpost : ∀ values : List Value,
        (iprop% ⌜values = []⌝ ∗
          globalPointsToAt 0 0 (.i32 1048560) ∗
          pointsTo_u64 0 1048552 42 ∗ pointsTo_u64 0 0 42) ⊢
        (iprop% ⌜values = []⌝) := by
      intro values
      iintro ⟨%hvalues, _Hresources⟩
      ipureexact hvalues
    iapply wp_mono hpost
    have halias := func0_alias_smallStep_wp
      (s := Stuckness.NotStuck) (E := ⊤)
      0 1 0 0 42 (by decide) (by decide)
    simp only [
      show ((0 : UInt32) <<< (3 % 32)) + 0 = 0 by decide] at halias
    iapply_frame halias


/-! ## Public initial-store bridge theorem -/

/-- The module's initial Wasm store with array `xs` written at byte offset `ptr`. -/
def func4InitialStore (ptr : UInt32) (xs : List UInt64) : Store Unit :=
  { («module».initialStore : Store Unit) with
    mem := Mem.writeWords64 («module».initialStore : Store Unit).mem ptr xs }

private def func4ScratchHeap : WasmHeapMap (Option UInt8) :=
  store32Heap (store32Heap (store64Heap ∅ 0 1048552 (0 : UInt64))
    0 1048568 (0 : UInt32)) 0 1048572 (0 : UInt32)

private theorem func4ScratchHeap_addr_lt
    (address : MemoryKey) (byte : Option UInt8)
    (h : get? func4ScratchHeap address = some byte) :
    address.addr.toNat < 1048576 := by
  by_contra hlt
  push Not at hlt
  have hne : ∀ n : UInt32, n.toNat < 1048576 →
      (⟨0, n⟩ : MemoryKey) ≠ address :=
    fun n hn heq => by
      have h := congrArg UInt32.toNat (congrArg MemoryKey.addr heq)
      change n.toNat = address.addr.toNat at h
      omega
  have hno : get? func4ScratchHeap address = none := by
    unfold func4ScratchHeap store32Heap store64Heap
    repeat rw [get?_insert_ne (hne _ (by decide))]
    exact get?_empty _
  simp [hno] at h

private theorem func4ScratchHeap_agrees :
    heapAgreesWithMem func4ScratchHeap
      (fun id => if id = 0 then some («module».initialStore : Store Unit).mem else none) := by
  let mem := («module».initialStore : Store Unit).mem
  have hmem : (fun id : Nat => if id = 0 then some mem else none) 0 = some mem := rfl
  unfold func4ScratchHeap
  apply_insert_physical_word32_sound hmem
  · apply_insert_physical_word32_sound hmem
    · apply_insert_physical_word64_sound hmem
      · exact heapAgreesWithMem_empty _
      · decide +kernel
    · decide +kernel
  · decide +kernel

private theorem func4ScratchHeap_inBounds :
    heapAddressesInBounds func4ScratchHeap
      (fun id => if id = 0 then some («module».initialStore : Store Unit).mem else none) := by
  let mem := («module».initialStore : Store Unit).mem
  have hmem : (fun id : Nat => if id = 0 then some mem else none) 0 = some mem := rfl
  unfold func4ScratchHeap
  apply_insert_physical_word32_inBounds hmem
  · apply_insert_physical_word32_inBounds hmem
    · apply_insert_physical_word64_inBounds hmem
      · exact heapAddressesInBounds_empty _
      · decide +kernel
    · decide +kernel
    · decide +kernel
  · decide +kernel
  · decide +kernel

private theorem func4ScratchHeap_pointsTo [WasmHeapGS Unit] :
    ([∗map] address ↦ value ∈ func4ScratchHeap,
      pointsTo (GF := WasmHeapGF Unit) (H := WasmHeapMap)
        address (DFrac.own 1) value) ⊢
      pointsTo_u64 0 1048552 (0 : UInt64) ∗
      pointsTo_u32 0 1048568 (0 : UInt32) ∗ pointsTo_u32 0 1048572 (0 : UInt32) := by
  unfold func4ScratchHeap
  iintro Hheap
  ihave ⟨Hlen, Hheap⟩ := store32Heap_pointsTo _ 0 1048572 (0 : UInt32)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hptr, Hheap⟩ := store32Heap_pointsTo _ 0 1048568 (0 : UInt32)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) $$ Hheap
  ihave ⟨Hscratch, _Hempty⟩ := store64Heap_pointsTo
    (∅ : WasmHeapMap (Option UInt8)) 0 1048552 (0 : UInt64)
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) $$ Hheap
  iframe

/-- Whole-array export bridge: the initial store with `xs` pre-written at `ptr`
terminates with `Mem.readWords64` equal to the swapped list.
No Iris witnesses are required from the caller. -/
theorem func4_initialStore_terminatesWith_array
    (ptr len i j : UInt32) (xs : List UInt64)
    (hlen : xs.length = len.toNat)
    (hi : i < len) (hj : j < len)
    (hroom : ptr.toNat + 8 * xs.length < UInt32.size)
    (hbase : 1048576 ≤ ptr.toNat)
    (hpages : ptr.toNat + 8 * xs.length ≤
        («module».initialStore : Store Unit).mem.pages * 65536) :
    Wasm.SmallStep.TerminatesWith
      (func4ConfigFromStore (func4InitialStore ptr xs) ptr len i j)
      (fun values store =>
        values = [] ∧
          Mem.readWords64 store.wasm.mem ptr xs.length =
            (xs.set i.toNat (xs.getD j.toNat 0)).set j.toNat (xs.getD i.toNat 0)) := by
  set initialMem := («module».initialStore : Store Unit).mem with hinitialMem
  set wasm : Store Unit := func4InitialStore ptr xs
  have hresolve_eq : (fun id : Nat =>
          if id = 0 then some (Mem.writeWords64 initialMem ptr xs) else none) =
      storeResolve (func4ConfigFromStore wasm ptr len i j).store :=
    singleMemoryResolve_eq_storeResolve _
      (Mem.writeWords64 initialMem ptr xs)
      (by simp [func4ConfigFromStore, wasm, func4InitialStore, hinitialMem])
      (by change («module».initialStore (α := Unit)).extraMems = []; decide +kernel)
  apply func4_store_terminatesWith_array wasm ptr len i j xs 0 0 0
    (heap64Aux func4ScratchHeap ptr xs) func4ExampleGlobals hlen hi hj hroom
  · rw [← hresolve_eq]
    exact heap64Aux_agrees func4ScratchHeap initialMem ptr xs
      func4ScratchHeap_agrees hroom
  · rw [← hresolve_eq]
    exact heap64Aux_inBounds func4ScratchHeap initialMem ptr xs
      func4ScratchHeap_inBounds hroom hpages
  · have hwasm : wasm.globals = («module».initialStore : Store Unit).globals := by
      simp [wasm, func4InitialStore]
    rw [hwasm]
    exact globalHeapAgrees_singleton (by decide +kernel)
  · intro _gs
    have hdisjoint : ∀ (address : MemoryKey) (byte : Option UInt8),
        get? func4ScratchHeap address = some byte →
        address.addr.toNat < ptr.toNat :=
      fun address byte haddr =>
        Nat.lt_of_lt_of_le (func4ScratchHeap_addr_lt address byte haddr) hbase
    iintro Hbytes
    ihave ⟨Harray, Hscr⟩ :=
      heap64Aux_pointsTo func4ScratchHeap ptr xs hdisjoint hroom $$ Hbytes
    ihave ⟨H552, H568, H572⟩ := func4ScratchHeap_pointsTo $$ Hscr
    iframe
  · intro _gs
    exact func4ExampleGlobals_pointsTo

end Project.SwapElements.SwapSepLogic
