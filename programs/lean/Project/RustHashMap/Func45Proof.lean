import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func47Proof

/-!
# Proof of the layout and overflow check of the `Error::new` chain

Local `func45` (absolute index 48) multiplies the element count by the
element size in 64 bits, rejects a product that does not fit in 32 bits,
rejects a size above `0x80000000` minus the alignment, and then calls the
allocate forwarder at absolute 50.

The chain fixes the element size and the alignment at 1 and the zero-fill
flag at 0, so the surviving test is `count <= 0x7fffffff`.  The
precondition gives it, which makes the overflow arm and the zero-count
arm dead.

The theorem is unconditional, because
`Project.RustHashMap.Func47Proof.func47_correct` is.
-/

namespace Project.RustHashMap.Func45Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.ErrorNewContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The 64-bit widening of a 32-bit word keeps its value. -/
private theorem toNat_ofNat_u32 (w : UInt32) :
    (UInt64.ofNat w.toNat).toNat = w.toNat := by
  have hsize : (UInt64.size : Nat) = 2 ^ 64 := rfl
  have hlt : w.toNat < 2 ^ 32 := w.toBitVec.isLt
  exact UInt64.toNat_ofNat_of_lt (by omega)

/-- The product of the count and an element size of 1 has no high word,
so the overflow arm of the body is dead. -/
private theorem high_word_zero (w : UInt32) :
    (UInt64.ofNat w.toNat) >>> (32 % 64) = 0 := by
  have hlt : w.toNat < 2 ^ 32 := w.toBitVec.isLt
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_shiftRight, toNat_ofNat_u32,
    show ((32 % 64 : UInt64).toNat % 64) = 32 from by decide,
    Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt hlt]
  rfl

/-- The low word of the product is the count itself. -/
private theorem low_word (w : UInt32) :
    UInt32.ofNat ((UInt64.ofNat w.toNat).toNat % 2 ^ 32) = w := by
  have hlt : w.toNat < 2 ^ 32 := w.toBitVec.isLt
  rw [toNat_ofNat_u32, Nat.mod_eq_of_lt hlt, UInt32.ofNat_toNat]

private theorem func45_index :
    Project.RustHashMap.«module».funcs[45]? =
      some Project.RustHashMap.func45Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func45_correct [WasmSmallStepGS hlc Universal.State] :
    Func45Spec (hlc := hlc) := by
  unfold Func45Spec CallContract callExpr
  intro sp out count heapId outBefore below storedCursor frontier
    history input output raised callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hcountPos, hcountLe⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 48
      Project.RustHashMap.func45Def (by decide) func45_index with Hmodule
  simp [Project.RustHashMap.func45Def, Project.RustHashMap.func45,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_localGet twp_extendUI32 twp_localGet twp_extendUI32
    twp_mulI64]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_constI64 twp_shrUI64 twp_wrapI64 twp_const]
  simp only [show UInt32.toNat 1 = 1 from rfl, show UInt64.ofNat 1 = 1 from rfl,
    UInt64.mul_one, high_word_zero count,
    show UInt32.ofNat ((0 : UInt64).toNat % 2 ^ 32) = 0 from rfl]
  iapply twp_ne (result := 0) (by decide)
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_wrapI64]
  simp only [low_word count]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_block twp_block twp_block twp_block twp_block twp_block
    twp_block twp_block twp_localGet twp_const twp_and]
  simp only [show (0 : UInt32) &&& 1 = 0 from by decide]
  iapply twp_brIfZero
  wasm_twp_pures [twp_localGet twp_const twp_localGet twp_sub]
  simp only [show (2147483648 : UInt32) - 1 = 2147483647 from by decide]
  have hcountLeU : count ≤ 2147483647 :=
    UInt32.le_iff_toNat_le.mpr (by simpa using hcountLe)
  iapply twp_leU (result := 1) (by rw [if_pos hcountLeU])
  wasm_twp_pures [twp_const twp_and]
  simp only [show (1 : UInt32) &&& 1 = 1 from by decide]
  iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  -- frame arithmetic
  have hdepth45 : func45Depth = 96 := rfl
  have hdepth47 : func47Depth = 48 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (96 : Nat) ≤ sp.toNat := by rw [hdepth45] at hspLow; exact hspLow
  have hframeNat : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le sp 48
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (48 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase48 : sp - UInt32.ofNat 48 = sp - 48 := by rfl
  have hcut : func45Depth - 48 = func47Depth := rfl
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp func45Depth 48 below (by decide) $$ Hbelow
  isimp only [hcut, hbase48] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 48) 48 (below.drop func47Depth) hbase48 $$ Hframe
  have hframeLen : below.length - func47Depth = 48 := by
    simpa using hframeLength
  ihave ⟨Hhead, Hrest⟩ :=
    ByteSlice_cut (sp - 48) (below.drop func47Depth) 16 (by omega) $$ Hframe
  ihave ⟨Hslot, Htop⟩ :=
    ByteSlice_cut (sp - 48 + UInt32.ofNat 16)
      ((below.drop func47Depth).drop 16) 8 (by simp; omega) $$ Hrest
  have hbaseTop : sp - 48 + UInt32.ofNat 16 + UInt32.ofNat 8
      = sp - 48 + UInt32.ofNat 24 := frame_offset (sp - 48) 16 8 24 rfl
  isimp only [hbaseTop] at Htop
  ihave ⟨%hcells, Harray⟩ :=
    ByteSlice_as_cells (sp - 48 + UInt32.ofNat 24)
      (((below.drop func47Depth).drop 16).drop 8) 6
      (by simp; omega) $$ Htop
  set cells := Slices.decodeWords (((below.drop func47Depth).drop 16).drop 8)
    with hcellsDef
  have haddr28 : sp - 48 + UInt32.ofNat 24 + 4 = sp - 48 + 28 := by
    rw [show (4 : UInt32) = UInt32.ofNat 4 from rfl,
      frame_offset (sp - 48) 24 4 28 rfl]
    rfl
  have haddr32 : sp - 48 + UInt32.ofNat 24 + 8 = sp - 48 + 32 := by
    rw [show (8 : UInt32) = UInt32.ofNat 8 from rfl,
      frame_offset (sp - 48) 24 8 32 rfl]
    rfl
  have haddr36 : sp - 48 + UInt32.ofNat 24 + 12 = sp - 48 + 36 := by
    rw [show (12 : UInt32) = UInt32.ofNat 12 from rfl,
      frame_offset (sp - 48) 24 12 36 rfl]
    rfl
  have haddr40 : sp - 48 + UInt32.ofNat 24 + 16 = sp - 48 + 40 := by
    rw [show (16 : UInt32) = UInt32.ofNat 16 from rfl,
      frame_offset (sp - 48) 24 16 40 rfl]
    rfl
  have haddr44 : sp - 48 + UInt32.ofNat 24 + 20 = sp - 48 + 44 := by
    rw [show (20 : UInt32) = UInt32.ofNat 20 from rfl,
      frame_offset (sp - 48) 24 20 44 rfl]
    rfl
  obtain ⟨h28, h28_1, h28_2, h28_3⟩ :=
    offset_facts (sp - 48) 28 28 (by decide) (by omega)
  obtain ⟨h32, h32_1, h32_2, h32_3⟩ :=
    offset_facts (sp - 48) 32 32 (by decide) (by omega)
  obtain ⟨h36, h36_1, h36_2, h36_3⟩ :=
    offset_facts (sp - 48) 36 36 (by decide) (by omega)
  obtain ⟨h40, h40_1, h40_2, h40_3⟩ :=
    offset_facts (sp - 48) 40 40 (by decide) (by omega)
  obtain ⟨h44, h44_1, h44_2, h44_3⟩ :=
    offset_facts (sp - 48) 44 44 (by decide) (by omega)
  -- `[f + 32] := 1`
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave ⟨Hcell, Hclose⟩ :=
    cell_focus (sp - 48 + UInt32.ofNat 24) 8 cells 2 _ 1
      (by simp [hcells]) rfl (by decide) $$ Harray
  isimp only [haddr32] at Hcell Hclose
  wasm_twp_rebind twp_store32 (address := sp - 48) (offset := 32) _
    h32 h32_1 h32_2 h32_3 with Hcell
  ihave Harray := Hclose $$ Hcell
  set cellsA := cells.set 2 1 with hA
  -- `[f + 36] := count`
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave ⟨Hcell, Hclose⟩ :=
    cell_focus (sp - 48 + UInt32.ofNat 24) 12 cellsA 3 _ count
      (by simp [hA, hcells]) rfl (by decide) $$ Harray
  isimp only [haddr36] at Hcell Hclose
  wasm_twp_rebind twp_store32 (address := sp - 48) (offset := 36) _
    h36 h36_1 h36_2 h36_3 with Hcell
  ihave Harray := Hclose $$ Hcell
  set cellsB := cellsA.set 3 count with hB
  -- `[f + 28] := 0`
  wasm_twp_pures [twp_localGet twp_const]
  ihave ⟨Hcell, Hclose⟩ :=
    cell_focus (sp - 48 + UInt32.ofNat 24) 4 cellsB 1 _ 0
      (by simp [hB, hA, hcells]) rfl (by decide) $$ Harray
  isimp only [haddr28] at Hcell Hclose
  wasm_twp_rebind twp_store32 (address := sp - 48) (offset := 28) _
    h28 h28_1 h28_2 h28_3 with Hcell
  ihave Harray := Hclose $$ Hcell
  set cellsC := cellsB.set 1 0 with hC
  -- `local 9 := [f + 32]`, `local 10 := [f + 36]`
  wasm_twp_pures [twp_localGet]
  ihave ⟨Hcell, Hclose⟩ :=
    cell_load (sp - 48 + UInt32.ofNat 24) 8 cellsC 2 1
      (by simp [hC, hB, hA, hcells]) (by simp [hC, hB, hA]) (by decide) $$ Harray
  isimp only [haddr32] at Hcell Hclose
  wasm_twp_rebind twp_load32 (address := sp - 48) (offset := 32)
    1 h32 h32_1 h32_2 h32_3 with Hcell
  ihave Harray := Hclose $$ Hcell
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  ihave ⟨Hcell, Hclose⟩ :=
    cell_load (sp - 48 + UInt32.ofNat 24) 12 cellsC 3 count
      (by simp [hC, hB, hA, hcells]) (by simp [hC, hB, hA]) (by decide) $$ Harray
  isimp only [haddr36] at Hcell Hclose
  wasm_twp_rebind twp_load32 (address := sp - 48) (offset := 36)
    count h36 h36_1 h36_2 h36_3 with Hcell
  ihave Harray := Hclose $$ Hcell
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the zero-count arm is dead
  have hcountNonzero : count ≠ 0 := by
    intro hzero; rw [hzero] at hcountPos; simp at hcountPos
  wasm_twp_pures [twp_localGet]
  iapply twp_eqz (result := 0) (by rw [if_neg hcountNonzero])
  iapply twp_brIfZero
  iapply twp_br (by rfl)
  simp only [List.take_zero, List.nil_append]
  wasm_twp_pures [twp_block twp_block twp_localGet twp_const twp_and]
  simp only [show (0 : UInt32) &&& 1 = 0 from by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const twp_add
    twp_localGet twp_localGet]
  have hslotAddr : (16 : UInt32) + (sp - 48) = sp - 48 + UInt32.ofNat 16 := by
    rw [UInt32.add_comm]
    rfl
  isimp only [← hslotAddr] at Hslot
  have hlowerNat : (sp - 48).toNat = sp.toNat - 48 := hframeNat
  have houtInnerNat : ((16 : UInt32) + (sp - 48)).toNat = sp.toNat - 32 := by
    rw [UInt32.add_comm, show (16 : UInt32) = UInt32.ofNat 16 from rfl,
      Slices.byteOffset_toNat (sp - 48) 16 (by omega)]
    omega
  have Hfwd : Func47Spec (hlc := hlc) :=
    Project.RustHashMap.Func47Proof.func47_correct
  unfold Func47Spec CallContract callExpr at Hfwd
  simp only [List.cons_append, List.nil_append] at Hfwd
  iapply Hfwd (sp := sp - 48) (out := 16 + (sp - 48))
    (unused := 27 + (sp - 48)) (size := count) (heapId := heapId)
    (outBefore := ((below.drop func47Depth).drop 16).take 8)
    (below := below.take func47Depth)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 count, .i32 0, .i32 1, .i32 1]
        locals := [.i32 (sp - 48), .i64 (UInt64.ofNat count.toNat), .i32 0,
          .i32 count, .i32 1, .i32 count, ValueType.i32.zero,
          ValueType.i32.zero, ValueType.i32.zero, ValueType.i32.zero,
          ValueType.i32.zero, ValueType.i32.zero, ValueType.i32.zero]
        values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl [Hsp]
  · unfold StackPointer
    iexact Hsp
  isplitl_exacts [Hlower Hslot Hbump Hstreams]
  isplitl_pureexact
    ⟨by simp; omega, by omega, by omega, hcountPos, hcountLe⟩
  isplit
  · iintro %ptr %blockId %contents %lower' %storedCursor' %frontier' %history'
    iintro Hruntime Hsp Hlower Hslot Hbump Hblock Hstreams
    unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    isimp only [StackPointer] at Hsp
    have hslotAddr' : (16 : UInt32) + (sp - 48) = sp - 48 + 16 := by
      rw [UInt32.add_comm]
    have haddr20 : sp - 48 + 16 + 4 = sp - 48 + 20 := by
      rw [show (16 : UInt32) = UInt32.ofNat 16 from rfl,
        show (4 : UInt32) = UInt32.ofNat 4 from rfl,
        frame_offset (sp - 48) 16 4 20 rfl]
      rfl
    isimp only [hslotAddr'] at Hslot
    ihave Hslotcells := cells_of_ByteSlice (sp - 48 + 16) [ptr, count] $$ Hslot
    isimp only [arrayAt, haddr20] at Hslotcells
    icases Hslotcells with ⟨Hptr, Hcount, _Hnil⟩
    obtain ⟨h16, h16_1, h16_2, h16_3⟩ :=
      offset_facts (sp - 48) 16 16 (by decide) (by omega)
    obtain ⟨h20, h20_1, h20_2, h20_3⟩ :=
      offset_facts (sp - 48) 20 20 (by decide) (by omega)
    obtain ⟨hout0, hout0_1, hout0_2, hout0_3⟩ :=
      offset_facts out 0 0 (by decide) (by omega)
    obtain ⟨hout4, hout4_1, hout4_2, hout4_3⟩ :=
      offset_facts out 4 4 (by decide) (by omega)
    obtain ⟨hout8, hout8_1, hout8_2, hout8_3⟩ :=
      offset_facts out 8 8 (by decide) (by omega)
    -- `local 14 := [f + 20]`
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 48) (offset := 20)
      count h20 h20_1 h20_2 h20_3 with Hcount
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    -- `[f + 40] := [f + 16]`
    wasm_twp_pures [twp_localGet twp_localGet]
    wasm_twp_rebind twp_load32 (address := sp - 48) (offset := 16)
      ptr h16 h16_1 h16_2 h16_3 with Hptr
    ihave ⟨Hcell, Hclose⟩ :=
      cell_focus (sp - 48 + UInt32.ofNat 24) 16 cellsC 4 _ ptr
        (by simp [hC, hB, hA, hcells]) rfl (by decide) $$ Harray
    isimp only [haddr40] at Hcell Hclose
    wasm_twp_rebind twp_store32 (address := sp - 48) (offset := 40) _
      h40 h40_1 h40_2 h40_3 with Hcell
    ihave Harray := Hclose $$ Hcell
    set cellsD := cellsC.set 4 ptr with hD
    -- `[f + 44] := local 14`
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Hcell, Hclose⟩ :=
      cell_focus (sp - 48 + UInt32.ofNat 24) 20 cellsD 5 _ count
        (by simp [hD, hC, hB, hA, hcells]) rfl (by decide) $$ Harray
    isimp only [haddr44] at Hcell Hclose
    wasm_twp_rebind twp_store32 (address := sp - 48) (offset := 44) _
      h44 h44_1 h44_2 h44_3 with Hcell
    ihave Harray := Hclose $$ Hcell
    set cellsE := cellsD.set 5 count with hE
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    -- `local 15 := [f + 40]`, and the null arm is dead
    ihave ⟨Hblock, %hptrNonzero⟩ :=
      Project.RustHashMap.Func41Proof.LiveBlock_ptr_ne_zero heapId blockId ptr
        (messageLayout count) contents $$ Hblock
    wasm_twp_pures [twp_localGet]
    ihave ⟨Hcell, Hclose⟩ :=
      cell_load (sp - 48 + UInt32.ofNat 24) 16 cellsE 4 ptr
        (by simp [hE, hD, hC, hB, hA, hcells]) (by simp [hE, hD]) (by decide) $$
        Harray
    isimp only [haddr40] at Hcell Hclose
    wasm_twp_rebind twp_load32 (address := sp - 48) (offset := 40)
      ptr h40 h40_1 h40_2 h40_3 with Hcell
    ihave Harray := Hclose $$ Hcell
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_block twp_const twp_localGet twp_localGet]
    iapply twp_select (selected := Value.i32 0) (by rw [if_pos hptrNonzero])
    wasm_twp_pures [twp_const twp_and]
    simp only [show (0 : UInt32) &&& 1 = 0 from by decide]
    iapply twp_eqz (result := 1) (by decide)
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    -- `local 17 := [f + 40]`
    wasm_twp_pures [twp_localGet]
    ihave ⟨Hcell, Hclose⟩ :=
      cell_load (sp - 48 + UInt32.ofNat 24) 16 cellsE 4 ptr
        (by simp [hE, hD, hC, hB, hA, hcells]) (by simp [hE, hD]) (by decide) $$
        Harray
    isimp only [haddr40] at Hcell Hclose
    wasm_twp_rebind twp_load32 (address := sp - 48) (offset := 40)
      ptr h40 h40_1 h40_2 h40_3 with Hcell
    ihave Harray := Hclose $$ Hcell
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    -- the three stores into the output slot
    ihave ⟨%houtCells, Houtarray⟩ :=
      ByteSlice_as_cells out outBefore 3 (by omega) $$ Hout
    set outCells := Slices.decodeWords outBefore with houtDef
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 4 outCells 1 _ count (by omega) rfl (by decide) $$
        Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 4) _
      hout4 hout4_1 hout4_2 hout4_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_pures [twp_localGet twp_localGet]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 8 (outCells.set 1 count) 2 _ ptr
        (by simp [houtCells]) rfl (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 8) _
      hout8 hout8_1 hout8_2 hout8_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    wasm_twp_pures [twp_localGet twp_const]
    ihave ⟨Houtcell, Houtclose⟩ :=
      cell_focus out 0 ((outCells.set 1 count).set 2 ptr) 0 _ 0
        (by simp [houtCells]) rfl (by decide) $$ Houtarray
    wasm_twp_rebind twp_store32 (address := out) (offset := 0) _
      hout0 hout0_1 hout0_2 hout0_3 with Houtcell
    ihave Houtarray := Houtclose $$ Houtcell
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.nil_append]
    -- restore the stack pointer and return
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (48 : UInt32) + (sp - 48) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    wasm_twp_rebind twp_globalSet with Hsp
    wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
    -- put the frame and the region back together
    ihave Hslotcells : arrayAt 0 (sp - 48 + 16) [ptr, count] $$ [Hptr Hcount]
    · isimp only [arrayAt, haddr20]
      iframe Hptr Hcount
    ihave Hslot :=
      ByteSlice_of_cells (sp - 48 + 16) [ptr, count]
        (by simp only [List.length_cons, List.length_nil,
              show (sp - 48 + 16).toNat = sp.toNat - 32 from by
                rw [show (16 : UInt32) = UInt32.ofNat 16 from rfl,
                  Slices.byteOffset_toNat (sp - 48) 16 (by omega)]
                omega]
            omega) $$ Hslotcells
    ihave Htop :=
      ByteSlice_of_cells (sp - 48 + UInt32.ofNat 24) cellsE
        (by rw [show cellsE.length = 6 from by
              simp [hE, hD, hC, hB, hA, hcells]]
            rw [show (sp - 48 + UInt32.ofNat 24).toNat = sp.toNat - 24 from by
              rw [Slices.byteOffset_toNat (sp - 48) 24 (by omega)]
              omega]
            omega) $$ Harray
    ihave Hrest :=
      ByteSlice_glue (sp - 48 + UInt32.ofNat 16)
        (WordCodec.u32le.serialize [ptr, count])
        (WordCodec.u32le.serialize cellsE) 8 (by simp) $$ [Hslot Htop]
    · isplitl_exact Hslot
      · irw_exact [hbaseTop] with Htop
    ihave Hframe :=
      ByteSlice_glue (sp - 48) ((below.drop func47Depth).take 16)
        (WordCodec.u32le.serialize [ptr, count]
          ++ WordCodec.u32le.serialize cellsE) 16
        (by simp; omega) $$ [Hhead Hrest]
    · isplitl_exact Hhead
      · iexact Hrest
    ihave Htop :=
      StackBelow_intro sp (sp - 48) 48
        ((below.drop func47Depth).take 16
          ++ (WordCodec.u32le.serialize [ptr, count]
            ++ WordCodec.u32le.serialize cellsE))
        (by simp [show cellsE.length = 6 from by
              simp [hE, hD, hC, hB, hA, hcells]]
            omega) hbase48 $$ Hframe
    ihave ⟨Hlower, %hlowerLength⟩ :=
      StackBelow_length (sp - 48) func47Depth lower' $$ Hlower
    isimp only [← hbase48, ← hcut] at Hlower
    ihave Hbelow :=
      frame_join sp func45Depth 48 lower'
        ((below.drop func47Depth).take 16
          ++ (WordCodec.u32le.serialize [ptr, count]
            ++ WordCodec.u32le.serialize cellsE))
        (by rw [hlowerLength, hcut]) (by decide) $$ [Hlower Htop]
    · isplitl_exact Hlower
      · iexact Htop
    ihave Hout :=
      ByteSlice_of_cells out (((outCells.set 1 count).set 2 ptr).set 0 0)
        (by rw [set_three outCells 0 count ptr houtCells]
            simpa using houtNowrap) $$ Houtarray
    isimp only [set_three outCells 0 count ptr houtCells,
      WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil] at Hout
    ihave Hsp : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %ptr %blockId %contents
      %(lower' ++ ((below.drop func47Depth).take 16
        ++ (WordCodec.u32le.serialize [ptr, count]
          ++ WordCodec.u32le.serialize cellsE)))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hbump Hblock Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams
