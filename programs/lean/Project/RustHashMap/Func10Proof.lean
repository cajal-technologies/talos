import Project.RustHashMap.GrowContract
import Project.RustHashMap.Func24Proof
import Project.RustHashMap.Func98Proof

/-!
# Proof of `RawVec::grow_amortized`

This file proves local `func10`, absolute `func 13`, against
`Project.RustHashMap.GrowContract.Func10Spec`.  The body is WAT lines
2555 to 2634 of `programs/rust/build/rust_hash_map/program.wat`.

The shape follows `Project.RustHashMap.Func23Proof`.  Both bodies commit a
16-byte frame, compute a new capacity, call absolute `func 27` with the
twelve result bytes at `frame + 4`, and write the answer into a two-word
header.  Three parts differ.  The element size and the alignment are
operands, not constants.  The capacity is a three-way maximum, because the
floor depends on the element size.  A second guard sits in front of the
capacity computation.

## The two dead arms

Row X-F13-ADD of `Analysis/scope-and-exclusions.md` is the `call 99` and
`unreachable` at WAT 2572.  The guard at WAT 2563 to 2570 adds the length
and the addition and compares the sum with the addition.  The
precondition gives `len + additional < UInt32.size`, so the sum does not
wrap, the comparison holds, and the arm is dead.

Row X-F13-OOM is the `call 99` and `unreachable` at WAT 2618, behind the
tag guard at WAT 2609 to 2613.  That row is live through `Func24Spec`:
the size bound of the precondition makes the new layout valid, so
absolute `func 27` reports the tag `0` and the arm is dead here, while
the out-of-memory arm of `Func24Spec` traps through `talos.oom`.
-/

namespace Project.RustHashMap.Func10Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.PairGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.GrowContract
open Project.RustHashMap.Func98Proof
open scoped Wasm.SmallStep.Outcome

private theorem func10_index :
    Project.RustHashMap.«module».funcs[10]? =
      some Project.RustHashMap.func10Def := by rfl

/-- The stack region that `growDepth` names is the sixteen-byte frame that
the body commits at `sp - 16`. -/
private theorem below_reserve [WasmHeapGS Universal.State]
    (sp : UInt32) (bytes : List UInt8) :
    StackBelow sp growDepth bytes ⊣⊢ StackReserve (sp - 16) bytes := by
  have hword : UInt32.ofNat growDepth = (16 : UInt32) := by rfl
  have hdepth : growDepth = 16 := rfl
  unfold StackBelow StackReserve
  rw [hword, hdepth]
  exact ⟨BI.BIBase.Entails.rfl, BI.BIBase.Entails.rfl⟩

set_option maxHeartbeats 2000000 in
/-- `RawVec::grow_amortized`.  It selects the new capacity, calls
`finish_grow`, and writes the new capacity and the new pointer back into
the two-word header. -/
theorem func10_correct [WasmSmallStepGS hlc Universal.State] :
    Func10Spec (hlc := hlc) := by
  unfold Func10Spec CallContract callExpr
  intro sp header cap ptr len additional align size source below heapId
    storedCursor frontier history input output raised callerLocals stack
    code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hcapacity, Hpointer, Hsource, Hbump,
    Hstreams, %hfacts, Hcont⟩
  obtain ⟨halign, hsizeCases, hheader, hsum, hgrow, hbound, hspLow⟩ :=
    hfacts
  have hsp : (16 : Nat) ≤ sp.toNat := hspLow
  have hsize : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsizeNat : size.toNat = 1 ∨ size.toNat = 8 := by
    rcases hsizeCases with h | h
    · exact Or.inl (by rw [h]; decide)
    · exact Or.inr (by rw [h]; decide)
  have halignNat : align.toNat = 1 ∨ align.toNat = 4 := by
    rcases halign with h | h
    · exact Or.inl (by rw [h]; decide)
    · exact Or.inr (by rw [h]; decide)
  have hsizePos : 0 < size.toNat := by rcases hsizeNat with h | h <;> omega
  let requiredNat : Nat := len.toNat + additional.toNat
  let minCapNat : Nat := if size.toNat = 1 then 8 else 4
  let newCapacityNat : Nat :=
    growCapacity cap.toNat requiredNat size.toNat
  let newCapacity : UInt32 := UInt32.ofNat newCapacityNat
  let oldLayout : AllocLayout :=
    { size := size.toNat * cap.toNat, alignment := align.toNat }
  let newLayout : AllocLayout :=
    { size := size.toNat * newCapacityNat, alignment := align.toNat }
  have hnewUnfold : newCapacityNat =
      max (max (2 * cap.toNat) requiredNat) minCapNat := rfl
  have hminCapNat : minCapNat = 8 ∨ minCapNat = 4 := by
    by_cases h : size.toNat = 1
    · exact Or.inl (by simp only [minCapNat, if_pos h])
    · exact Or.inr (by simp only [minCapNat, if_neg h])
  have hmidLe : max (2 * cap.toNat) requiredNat ≤ newCapacityNat := by
    rw [hnewUnfold]; exact le_max_left _ _
  have hminLe : minCapNat ≤ newCapacityNat := by
    rw [hnewUnfold]; exact le_max_right _ _
  have hdoubleLe : 2 * cap.toNat ≤ newCapacityNat :=
    Nat.le_trans (le_max_left _ _) hmidLe
  have hreqLe : requiredNat ≤ newCapacityNat :=
    Nat.le_trans (le_max_right _ _) hmidLe
  have hbound' : size.toNat * newCapacityNat ≤ 2147483648 - align.toNat :=
    hbound
  have hmulGe : newCapacityNat ≤ size.toNat * newCapacityNat :=
    Nat.le_mul_of_pos_left _ hsizePos
  have hnewCapLe : newCapacityNat ≤ 2147483647 := by
    rcases halignNat with h | h <;> omega
  have hnewCapLt : newCapacityNat < UInt32.size := by rw [hsize]; omega
  have hmidLt : max (2 * cap.toNat) requiredNat < UInt32.size := by
    rw [hsize]; omega
  have hminLt : minCapNat < UInt32.size := by rw [hsize]; omega
  have hdoubleBound : 2 * cap.toNat < UInt32.size := by rw [hsize]; omega
  have hrequiredLt : requiredNat < UInt32.size := hsum
  have hcapLt : cap.toNat < requiredNat := hgrow
  have hnewPos : 0 < newCapacityNat := by omega
  have hnewCapacityWord : newCapacity.toNat = newCapacityNat :=
    UInt32.toNat_ofNat_of_lt' hnewCapLt
  have hnewValid : newLayout.Valid := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show 0 < size.toNat * newCapacityNat
      rcases hsizeNat with h | h <;> rw [h] <;> omega
    · show 0 < align.toNat
      rcases halignNat with h | h <;> omega
    · show ∃ exponent, align.toNat = 2 ^ exponent
      rcases halignNat with h | h
      · exact ⟨0, by rw [h]; norm_num⟩
      · exact ⟨2, by rw [h]; norm_num⟩
    · show align.toNat ≤ 2147483648
      rcases halignNat with h | h <;> omega
    · show size.toNat * newCapacityNat ≤ 2147483648 - align.toNat
      exact hbound'
    · show size.toNat * newCapacityNat < UInt32.size
      rw [hsize]
      rcases halignNat with h | h <;> omega
    · show align.toNat < UInt32.size
      rw [hsize]
      rcases halignNat with h | h <;> omega
  have holdNew : oldLayout.size < newLayout.size := by
    show size.toNat * cap.toNat < size.toNat * newCapacityNat
    rcases hsizeNat with h | h <;> rw [h] <;> omega
  have hframe : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16
      (UInt32.le_iff_toNat_le.mpr (by simpa using hsp))]
    rfl
  have hf4 : (sp - 16 + 4).toNat = (sp - 16).toNat + 4 := by
    simpa using Slices.byteOffset_toNat (sp - 16) 4 (by omega)
  have hf8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by
    simpa using Slices.byteOffset_toNat (sp - 16) 8 (by omega)
  have hf4_1 : (sp - 16 + 4 + 1).toNat = (sp - 16 + 4).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 4) 1 (by omega)
  have hf4_2 : (sp - 16 + 4 + 2).toNat = (sp - 16 + 4).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 4) 2 (by omega)
  have hf4_3 : (sp - 16 + 4 + 3).toNat = (sp - 16 + 4).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 4) 3 (by omega)
  have hf8_1 : (sp - 16 + 8 + 1).toNat = (sp - 16 + 8).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 8) 1 (by omega)
  have hf8_2 : (sp - 16 + 8 + 2).toNat = (sp - 16 + 8).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 8) 2 (by omega)
  have hf8_3 : (sp - 16 + 8 + 3).toNat = (sp - 16 + 8).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (sp - 16 + 8) 3 (by omega)
  have hh0_1 : (header + 1).toNat = header.toNat + 1 := by
    simpa using Slices.byteOffset_toNat header 1 (by omega)
  have hh0_2 : (header + 2).toNat = header.toNat + 2 := by
    simpa using Slices.byteOffset_toNat header 2 (by omega)
  have hh0_3 : (header + 3).toNat = header.toNat + 3 := by
    simpa using Slices.byteOffset_toNat header 3 (by omega)
  have hh4 : (header + 4).toNat = header.toNat + 4 := by
    simpa using Slices.byteOffset_toNat header 4 (by omega)
  have hh4_1 : (header + 4 + 1).toNat = (header + 4).toNat + 1 := by
    simpa using Slices.byteOffset_toNat (header + 4) 1 (by omega)
  have hh4_2 : (header + 4 + 2).toNat = (header + 4).toNat + 2 := by
    simpa using Slices.byteOffset_toNat (header + 4) 2 (by omega)
  have hh4_3 : (header + 4 + 3).toNat = (header + 4).toNat + 3 := by
    simpa using Slices.byteOffset_toNat (header + 4) 3 (by omega)
  have hrequiredWord : (len + additional).toNat = requiredNat := by
    show (len + additional).toNat = len.toNat + additional.toNat
    rw [UInt32.toNat_add]
    exact Nat.mod_eq_of_lt hsum
  have hrequiredOfNat : UInt32.ofNat requiredNat = len + additional := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_ofNat_of_lt' hrequiredLt, hrequiredWord]
  have hgeCond : additional ≤ len + additional :=
    UInt32.le_iff_toNat_le.mpr (by rw [hrequiredWord]; omega)
  have hgeWord :
      (1 : UInt32) = if len + additional ≥ additional then 1 else 0 :=
    (if_pos hgeCond).symm
  have hdoubleWord : cap <<< (1 : UInt32) =
      UInt32.ofNat (2 * cap.toNat) := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_shiftLeft,
      show (1 : UInt32).toNat % 32 = 1 by decide,
      Nat.shiftLeft_eq, pow_one,
      Nat.mod_eq_of_lt (by
        norm_num [UInt32.size] at hdoubleBound ⊢; omega),
      UInt32.toNat_ofNat_of_lt' hdoubleBound]
    omega
  have hselectOne :
      (if (if len + additional > UInt32.ofNat (2 * cap.toNat) then
            (1 : UInt32) else 0) ≠ 0 then
          Value.i32 (len + additional)
        else Value.i32 (UInt32.ofNat (2 * cap.toNat))) =
        Value.i32 (UInt32.ofNat (max (2 * cap.toNat) requiredNat)) := by
    by_cases hcmp : len + additional > UInt32.ofNat (2 * cap.toNat)
    · rw [if_pos hcmp, if_pos (by decide : (1 : UInt32) ≠ 0)]
      have hn : 2 * cap.toNat < requiredNat := by
        change UInt32.ofNat (2 * cap.toNat) < len + additional at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hdoubleBound, hrequiredWord] at hcmp
        exact hcmp
      rw [max_eq_right (by omega), hrequiredOfNat]
    · rw [if_neg hcmp, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      have hn : requiredNat ≤ 2 * cap.toNat := by
        change ¬ UInt32.ofNat (2 * cap.toNat) < len + additional at hcmp
        rw [UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hdoubleBound, hrequiredWord] at hcmp
        omega
      rw [max_eq_left hn]
  have hselectTwo :
      (if (if size = 1 then (1 : UInt32) else 0) ≠ 0 then
          Value.i32 8 else Value.i32 4) =
        Value.i32 (UInt32.ofNat minCapNat) := by
    by_cases hs : size = 1
    · rw [if_pos hs, if_pos (by decide : (1 : UInt32) ≠ 0)]
      have hn : size.toNat = 1 := by rw [hs]; decide
      show Value.i32 8 = Value.i32 (UInt32.ofNat minCapNat)
      rw [show minCapNat = 8 by simp only [minCapNat, if_pos hn]]
      rfl
    · rw [if_neg hs, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      have hn : size.toNat ≠ 1 := by
        intro hcontra
        exact hs (UInt32.toNat_inj.mp (by rw [hcontra]; decide))
      show Value.i32 4 = Value.i32 (UInt32.ofNat minCapNat)
      rw [show minCapNat = 4 by simp only [minCapNat, if_neg hn]]
      rfl
  have hselectThree :
      (if (if UInt32.ofNat (max (2 * cap.toNat) requiredNat) >
            UInt32.ofNat minCapNat then (1 : UInt32) else 0) ≠ 0 then
          Value.i32 (UInt32.ofNat (max (2 * cap.toNat) requiredNat))
        else Value.i32 (UInt32.ofNat minCapNat)) =
        Value.i32 newCapacity := by
    by_cases hcmp : UInt32.ofNat (max (2 * cap.toNat) requiredNat) >
        UInt32.ofNat minCapNat
    · rw [if_pos hcmp, if_pos (by decide : (1 : UInt32) ≠ 0)]
      have hn : minCapNat < max (2 * cap.toNat) requiredNat := by
        change UInt32.ofNat minCapNat <
          UInt32.ofNat (max (2 * cap.toNat) requiredNat) at hcmp
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hminLt,
          UInt32.toNat_ofNat_of_lt' hmidLt] at hcmp
        exact hcmp
      show Value.i32 (UInt32.ofNat (max (2 * cap.toNat) requiredNat)) =
        Value.i32 (UInt32.ofNat newCapacityNat)
      rw [hnewUnfold, max_eq_left (Nat.le_of_lt hn)]
    · rw [if_neg hcmp, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      have hn : max (2 * cap.toNat) requiredNat ≤ minCapNat := by
        change ¬ UInt32.ofNat minCapNat <
          UInt32.ofNat (max (2 * cap.toNat) requiredNat) at hcmp
        rw [UInt32.lt_iff_toNat_lt, UInt32.toNat_ofNat_of_lt' hminLt,
          UInt32.toNat_ofNat_of_lt' hmidLt] at hcmp
        omega
      show Value.i32 (UInt32.ofNat minCapNat) =
        Value.i32 (UInt32.ofNat newCapacityNat)
      rw [hnewUnfold, max_eq_right hn]
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 13
      Project.RustHashMap.func10Def (by decide) func10_index with Hmodule
  simp [Project.RustHashMap.func10Def, Project.RustHashMap.func10,
    Function.toLocals, Function.numParams]
  ihave Hreserve := (below_reserve sp below).mp $$ Hbelow
  ihave HreserveParts := (StackReserve_split (sp - 16) below).mp $$ Hreserve
  icases HreserveParts with
    ⟨%headBytes, %growBefore, %hbelowSplit, Hhead, HgrowBefore⟩
  have hheadWord : UInt32.ofNat headBytes.length = 4 := by
    rw [hbelowSplit.2.1]; decide
  have hgrowAddress :
      sp - 16 + UInt32.ofNat headBytes.length = sp - 16 + 4 := by
    rw [hheadWord]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_block twp_localGet twp_localGet twp_add]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_geU (result := 1) hgeWord
  iapply twp_brIf (by decide) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 4 (sp - 16)]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32_addr cap hh0_1 hh0_2 hh0_3 with Hcapacity
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := header) (offset := 4) ptr
      (by simpa using hh4) hh4_1 hh4_2 hh4_3 with Hpointer
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
  rw [show (1 : UInt32) % 32 = 1 by decide, hdoubleWord]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_gtU]
  iapply twp_select
    (selected := .i32 (UInt32.ofNat (max (2 * cap.toNat) requiredNat)))
    hselectOne.symm
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_const twp_localGet twp_const twp_eq]
  iapply twp_select (selected := .i32 (UInt32.ofNat minCapNat))
    hselectTwo.symm
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_gtU]
  iapply twp_select (selected := .i32 newCapacity) hselectThree.symm
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet]
  have Hfinish : Func24Spec (hlc := hlc) :=
    Project.RustHashMap.Func24Proof.func24_correct
  unfold Func24Spec CallContract callExpr at Hfinish
  simp only [List.cons_append, List.nil_append] at Hfinish
  iapply Hfinish (result := sp - 16 + 4) (oldCapacity := cap)
    (oldPtr := ptr) (newCapacity := newCapacity) (alignment := align)
    (elemSize := size) (oldLayout := oldLayout) (newLayout := newLayout)
    (source := source) (resultBefore := growBefore) (heapId := heapId)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals := {
      params := [.i32 header, .i32 (UInt32.ofNat minCapNat),
        .i32 newCapacity, .i32 align, .i32 size]
      locals := [.i32 (sp - 16)]
      values := [] })
    (stack := [])
  ihave HgrowBeforeAt := byteSlice_address_eq hgrowAddress $$ HgrowBefore
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exacts [HgrowBeforeAt Hsource Hbump Hstreams]
  isplitl_pureexact (by
    refine ⟨hbelowSplit.2.2, by rw [hf4]; omega, rfl, ?_, rfl, rfl,
      halignNat, hnewValid, holdNew⟩
    show size.toNat * newCapacityNat = size.toNat * newCapacity.toNat
    rw [hnewCapacityWord])
  unfold FinishContinuation
  cases hdecision : classifyBump frontier newLayout with
  | oom =>
      have hdecisionCont :
          classifyBump frontier
            { size := size.toNat *
                growCapacity cap.toNat
                  (len.toNat + additional.toNat) size.toNat,
              alignment := align.toNat } = .oom := by
        simpa only [newLayout, newCapacityNat, requiredNat] using hdecision
      iintro Hresult Hsource Hbump Hstreams
      ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
      ihave Hreserve : StackReserve (sp - 16) below $$ [Hhead HresultAt]
      · iapply (StackReserve_split (sp - 16) below).mpr
        iexists headBytes, growBefore
        isplitr_pureexact hbelowSplit
        · iframe
      ihave Hbelow := (below_reserve sp below).mpr $$ Hreserve
      ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      isimp only [GrowContinuation, hdecisionCont] at Hcont
      iapply Hcont $$ Hsp' Hbelow Hcapacity Hpointer Hsource Hbump Hstreams
  | success newPtr finish =>
      have hdecisionCont :
          classifyBump frontier
            { size := size.toNat *
                growCapacity cap.toNat
                  (len.toNat + additional.toNat) size.toNat,
              alignment := align.toNat } = .success newPtr finish := by
        simpa only [newLayout, newCapacityNat, requiredNat] using hdecision
      isplit
      · iintro %newBytes Hruntime Hresult Hbump Hblock %hcopy Hstreams
        iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        isimp only [Slices.ByteSlice, finishResultBytes] at Hresult
        icases Hresult with ⟨%hresultNowrap, HresultBytes⟩
        ihave Harray : arrayAt 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size] $$ [HresultBytes]
        · iapply (Slices.arrayAt_eq_wordCells 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size]).mpr
          iexact HresultBytes
        isimp only [arrayAt] at Harray
        icases Harray with ⟨Htag, HnewPointer, HnewSize, _Hemp⟩
        wasm_twp_pures [twp_block twp_localGet]
        wasm_twp_rebind twp_load32 (address := sp - 16) (offset := 4) 0
            (by simpa using hf4) hf4_1 hf4_2 hf4_3 with Htag
        wasm_twp_pures [twp_const]
        iapply twp_ne (result := 1) (by decide)
        iapply twp_brIf (by decide) (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        wasm_twp_pures [twp_localGet]
        have hplus8 : sp - 16 + 4 + 4 = sp - 16 + 8 := by
          simp only [UInt32.add_assoc, UInt32.reduceAdd]
        ihave HnewPointer' : pointsTo_u32 0 (sp - 16 + 8) newPtr $$
            [HnewPointer]
        · irw_exact [← hplus8] with HnewPointer
        wasm_twp_bind twp_load32 (address := sp - 16) (offset := 8) newPtr
            (by simpa using hf8) hf8_1 hf8_2 hf8_3 with HnewPointer' =>
            HnewPointer
        wasm_twp_localSet [List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub, List.set]
        wasm_twp_pures [twp_localGet twp_localGet]
        ihave Hcapacity' :=
          pointsTo_u32_address_eq (UInt32.add_zero header).symm $$
            Hcapacity
        wasm_twp_bind twp_store32 (address := header) (offset := 0) cap
            (by simp) (by simpa using hh0_1) (by simpa using hh0_2)
            (by simpa using hh0_3) with Hcapacity' => Hcapacity
        isimp only [UInt32.add_zero] at Hcapacity
        wasm_twp_pures [twp_localGet twp_localGet]
        wasm_twp_rebind twp_store32 (address := header) (offset := 4) ptr
            (by simpa using hh4) hh4_1 hh4_2 hh4_3 with Hpointer
        wasm_twp_pures [twp_localGet twp_const twp_add]
        rw [show (16 : UInt32) + (sp - 16) = sp by
          rw [UInt32.add_comm, UInt32.sub_add_cancel]]
        wasm_twp_rebind twp_globalSet with Hsp
        wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
        simp only [List.take_zero, List.nil_append]
        ihave Harray : arrayAt 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size] $$
            [Htag HnewPointer HnewSize]
        · isimp only [arrayAt]
          isplitl_exact Htag
          isplitl [HnewPointer]
          · iapply pointsTo_u32_address_eq hplus8.symm
            iexact HnewPointer
          isplitl_exact HnewSize
          · itrivial
        ihave HresultBytes : Slices.WordCells 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size] $$ [Harray]
        · iapply (Slices.arrayAt_eq_wordCells 0 (sp - 16 + 4)
            [0, newPtr, UInt32.ofNat newLayout.size]).mp
          iexact Harray
        ihave Hresult : Slices.ByteSlice 0 (sp - 16 + 4)
            (finishResultBytes newPtr (UInt32.ofNat newLayout.size)) $$
            [HresultBytes]
        · unfold Slices.ByteSlice finishResultBytes
          iframe_pureexact using [HresultBytes] => hresultNowrap
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve (sp - 16)
            (headBytes ++
              finishResultBytes newPtr (UInt32.ofNat newLayout.size)) $$
            [Hhead HresultAt]
        · iapply (StackReserve_split (sp - 16)
            (headBytes ++
              finishResultBytes newPtr (UInt32.ofNat newLayout.size))).mpr
          iexists headBytes,
            finishResultBytes newPtr (UInt32.ofNat newLayout.size)
          isplitr_pureexact
            ⟨rfl, hbelowSplit.2.1, finishResultBytes_length _ _⟩
          · iframe
        ihave Hbelow := (below_reserve sp
          (headBytes ++
            finishResultBytes newPtr
              (UInt32.ofNat newLayout.size))).mpr $$ Hreserve
        ihave Hsp' : StackPointer sp $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        iclose_map_runtime Hruntime with Hmodule Henv
        isimp only [GrowContinuation, hdecisionCont,
          GrowContract.growHistory] at Hcont
        ihave Hnormal := BI.and_elim_l $$ Hcont
        isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
        ihave Hnormal := Hnormal $$ %newBytes
          %(headBytes ++
            finishResultBytes newPtr (UInt32.ofNat newLayout.size))
        iapply Hnormal $$ Hruntime Hsp' Hbelow Hcapacity Hpointer Hblock
          Hbump %hcopy Hstreams
      · iintro Hresult Hsource Hbump Hstreams
        ihave HresultAt := byteSlice_address_eq hgrowAddress.symm $$ Hresult
        ihave Hreserve : StackReserve (sp - 16) below $$ [Hhead HresultAt]
        · iapply (StackReserve_split (sp - 16) below).mpr
          iexists headBytes, growBefore
          isplitr_pureexact hbelowSplit
          · iframe
        ihave Hbelow := (below_reserve sp below).mpr $$ Hreserve
        ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
        · unfold StackPointer
          iexact Hsp
        isimp only [GrowContinuation, hdecisionCont] at Hcont
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ Hsp' Hbelow Hcapacity Hpointer Hsource Hbump
          Hstreams

end Project.RustHashMap.Func10Proof
