import Project.RustHashMap.Func14Proof
import Project.RustHashMap.Func14ResizeWalk
import Project.RustHashMap.DeallocNoop
import Project.RustHashMap.Func55Proof
import Project.RustHashMap.MapOpContracts

/-!
# Proof of the resize arm of absolute `func 17`

This file proves `MapOpContracts.Func14ResizeSpec`.  That contract is
absolute `func 17`, `RawTableInner::reserve_rehash_inner`, on the path
that absolute `func 18` takes: the old table is a general table with no
growth left, and the addition is one item.

`Project.RustHashMap.Func14Proof.func14_correct_of` proves the same body
on the static empty table.  The two proofs share the block split, the
phase names and the allocation.  This file imports them.

The live path here is longer.  The old table has items, so the walk of
WAT 3746 to 4083 runs and the free of WAT 4098 to 4117 runs.
`Project.RustHashMap.Func14ResizeWalk.twp_resize_walk` proves the walk.

The rehash-in-place arm of WAT 3116 to 3640 stays dead.  The guard at
WAT 3063 asks for `items + 1 <= full_cap / 2`, and a clean table with no
growth left has `items = full_cap`.
-/

namespace Project.RustHashMap.Func14Resize

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.VecGrow
open Project.RustHashMap.Func14Capacity
open Project.RustHashMap.Func14Proof
open Project.RustHashMap.Func14ResizeWalk
open Project.RustHashMap.MapOpContracts
open scoped Wasm.SmallStep.Outcome

variable [WasmSmallStepGS hlc Universal.State]

/-- The normal arm of `Func14ResizeSpec`, as an open proposition.  The
stage lemmas below end with it. -/
@[reducible] def NormalArm (sp out table hasher : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (heapId : GName)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value) (code : Program)
    (arity : Nat) (remainder : List Value) (controls : List ControlFrame)
    (calls : List CallFrame) (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ word1 : UInt32, ∀ below' : List UInt8,
    ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
    ∀ history' : AllocationHistory,
    RuntimeContext -∗
    StackPointer sp -∗
    StackBelow sp resizeDepth below' -∗
    Slices.ByteSlice 0 out
      (WordCodec.u32le.encode okTag ++ WordCodec.u32le.encode word1) -∗
    HashMap.Table.TableAt 0 table
      (HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1) t 1) -∗
    pointsTo_u64 0 hasher k0 -∗
    pointsTo_u64 0 (hasher + 8) k1 -∗
    BumpHeap heapId storedCursor' frontier' history' -∗
    Streams input output raised -∗
    ResumeWP [] callerLocals stack code arity remainder controls calls s E Φ)

set_option maxHeartbeats 2000000 in
/-- WAT 4119 to 4129: the result slot and the stack pointer.  Both the
free arm and the arm that skips the free reach this code. -/
theorem twp_resize_epilogue
    (sp out table hasher word1 : UInt32) (k0 k1 : UInt64)
    (t : HashMap.Table UInt32 UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    {p1 p3 : UInt32} {l6 l7 l8 l9 l10 l11 l12 w13 w14 w15 w16 w17 w18 w19
      w20 w21 l22 l23 w24 l25 w26 l27 : Value}
    (houtLength : outBefore.length = 8)
    (houtNowrap : out.toNat + 8 < UInt32.size) :
    iprop(RuntimeContext ∗
      StackPointer (sp - 32) ∗
      StackBelow sp resizeDepth below ∗
      Slices.ByteSlice 0 out outBefore ∗
      HashMap.Table.TableAt 0 table
        (HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1) t 1) ∗
      pointsTo_u64 0 hasher k0 ∗
      pointsTo_u64 0 (hasher + 8) k1 ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      NormalArm sp out table hasher k0 k1 t heapId input output raised
        callerLocals stack code arity remainder controls calls s E Φ) ⊢
      WP (Expr.running
          ⟨⟨[.i32 out, .i32 p1, .i32 word1, .i32 p3, .i32 okTag],
              rawLocals (.i32 (sp - 32)) l6 l7 l8 l9 l10 l11 l12 w13 w14
                w15 w16 w17 w18 w19 w20 w21 l22 l23 w24 l25 w26 l27, []⟩,
            epiloguePhase, 0, [], [],
            callerFrame callerLocals stack code arity remainder controls ::
              calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Htable, Hk0, Hk1, Hbump, Hstreams,
    Hnormal⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  have hsz : UInt32.size = 4294967296 := rfl
  have h4lit : (4 : UInt32).toNat = 4 := rfl
  have hlowLength : (outBefore.take 4).length = 4 := by
    rw [List.length_take, houtLength]
    omega
  have hhighLength : (outBefore.drop 4).length = 4 := by
    rw [List.length_drop, houtLength]
  have ho4 := offset_facts out 4 4 rfl (by omega)
  have ho0 := offset_facts out 0 0 rfl (by omega)
  ihave ⟨Hlow, Hhigh⟩ := ByteSlice_cut out outBefore 4 (by omega) $$ Hout
  isimp only [show UInt32.ofNat 4 = (4 : UInt32) from rfl] at Hhigh
  ihave ⟨Hword4, Hwand4⟩ :=
    Slices.ByteSlice_storeWordFocus 0 (out + 4) (outBefore.drop 4) word1
      hhighLength (by rw [ho4.1, h4lit, hsz]; omega) $$ Hhigh
  ihave ⟨Hword0, Hwand0⟩ :=
    Slices.ByteSlice_storeWordFocus 0 out (outBefore.take 4) okTag
      hlowLength (by rw [hsz]; omega) $$ Hlow
  ihave Hword0 := pointsTo_u32_at (UInt32.add_zero out) $$ Hword0
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 4)
    (WordCodec.decodeU32 (outBefore.drop 4))
    ho4.1 ho4.2.1 ho4.2.2.1 ho4.2.2.2 with Hword4
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 0)
    (WordCodec.decodeU32 (outBefore.take 4))
    ho0.1 ho0.2.1 ho0.2.2.1 ho0.2.2.2 with Hword0
  ihave Hword0 := pointsTo_u32_at (UInt32.add_zero out).symm $$ Hword0
  ihave Hlow := Hwand0 $$ Hword0
  ihave Hhigh := Hwand4 $$ Hword4
  ihave Hout := ByteSlice_glue out
    (WordCodec.u32le.serialize [okTag])
    (WordCodec.u32le.serialize [word1]) 4 (by decide)
    $$ [Hlow Hhigh]
  · isplitl_exact Hlow
    · irw_exact [show UInt32.ofNat 4 = (4 : UInt32) from rfl] with Hhigh
  isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil] at Hout
  isimp only [StackPointer] at Hsp
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (32 : UInt32) + (sp - 32) = sp by
    rw [UInt32.add_comm, UInt32.sub_add_cancel]]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  iclose_map_runtime Hruntime with Hmodule Henv
  ihave Hsp : StackPointer sp $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  isimp only [NormalArm] at Hnormal
  ihave Hnormal := Hnormal $$ %word1 %below %storedCursor %frontier
    %history
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
  iapply Hnormal $$ Hruntime Hsp Hbelow Hout Htable Hk0 Hk1 Hbump Hstreams

/-- The two counters do not touch the control bytes. -/
theorem withCounters_ctrl (x : HashMap.Table UInt32 UInt32) (a g : Nat) :
    (HashMap.Table.withCounters x a g).ctrl = x.ctrl := rfl

/-- The two counters do not touch the buckets. -/
theorem withCounters_slots (x : HashMap.Table UInt32 UInt32) (a g : Nat) :
    (HashMap.Table.withCounters x a g).slots = x.slots := rfl

/-- A subtraction of two small counts, as words. -/
theorem ofNat_sub_ofNat {a b : Nat} (hba : b ≤ a) (ha : a < 4294967296) :
    UInt32.ofNat a - UInt32.ofNat b = UInt32.ofNat (a - b) := by
  have hsize : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' (by omega),
    UInt32.toNat_ofNat_of_lt' (by omega),
    UInt32.toNat_ofNat_of_lt' (by omega)]
  omega

set_option maxRecDepth 1048576 in
/-- The two block splits name the same tail of the resize block. -/
theorem resize_tail_eq :
    Func14Proof.resizeTail = Func14ResizeWalk.resizeTail := by rfl


set_option maxRecDepth 1048576 in
/-- WAT 4098 to 4117: the free of the old control array.  The size is
`9 * buckets + 8`, the same layout that the allocation asked for. -/
theorem shape_free_tail :
    freeTail =
      [.localGet 7, .localGet 8, .const 3, .shl, .localTee 2, .add,
        .const 9, .add, .localTee 7, .eqz, .br_if 0, .localGet 10,
        .localGet 2, .sub, .localGet 7, .const 8, .call 60] := by rfl

set_option maxHeartbeats 2000000 in
/-- WAT 4085 to 4129: the three header writes, the free of the old control
array and the epilogue.  The item count at offset 12 keeps the value that
the old table had, because the walk moved every item. -/
theorem twp_resize_tail
    (sp out table hasher : UInt32) (k0 k1 : UInt64)
    (t n : HashMap.Table UInt32 UInt32) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (ctrlNew ctrlOldPtr : UInt32)
    {oldCtrlW oldHdrMask oldHdrGrowth : UInt32}
    {p2 p3 p4 : UInt32}
    {l12 w13 w14 w15 w16 w17 w18 w19 w20 w21 l22 l23 w24 w26 l27 : Value}
    {newGrowthW newMaskW : UInt32}
    (hmaskW : newMaskW = UInt32.ofNat (n.buckets - 1))
    (houtLength : outBefore.length = 8)
    (houtNowrap : out.toNat + 8 < UInt32.size)
    (htableNowrap : table.toNat + 16 < UInt32.size)
    (hbPos : 0 < t.buckets) (hbHigh : t.buckets ≤ 2 ^ 27)
    (hbShape : t.buckets = 1 ∨ 4 ≤ t.buckets)
    (hitems : n.items = t.items)
    (hroom : 8 * n.buckets ≤ ctrlNew.toNat)
    (hbuck : 1 < n.buckets)
    (hgrowthW : newGrowthW - UInt32.ofNat t.items
      = UInt32.ofNat n.growthLeft)
    (hres : HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1) t 1 = n) :
    iprop(RuntimeContext ∗
      StackPointer (sp - 32) ∗
      StackBelow sp resizeDepth below ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 table oldCtrlW ∗
      pointsTo_u32 0 (table + 4) oldHdrMask ∗
      pointsTo_u32 0 (table + 8) oldHdrGrowth ∗
      pointsTo_u32 0 (table + 12) (UInt32.ofNat t.items) ∗
      Slices.ByteSlice 0 ctrlNew n.ctrl ∗
      HashMap.Table.slotsBefore 0 ctrlNew n.slots ∗
      pointsTo_u64 0 hasher k0 ∗
      pointsTo_u64 0 (hasher + 8) k1 ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      NormalArm sp out table hasher k0 k1 t heapId input output raised
        callerLocals stack code arity remainder controls calls s E Φ) ⊢
      WP (Expr.running
          ⟨⟨[.i32 out, .i32 table, .i32 p2, .i32 p3, .i32 p4],
              rawLocals (.i32 (sp - 32)) (.i32 (UInt32.ofNat t.items))
                (.i32 (UInt32.ofNat (t.buckets - 1)))
                (.i32 (UInt32.ofNat t.buckets)) (.i32 ctrlNew)
                (.i32 ctrlOldPtr) (.i32 newMaskW)
                l12 w13 w14 w15 w16 w17 w18 w19 w20 w21 l22 l23 w24
                (.i32 newGrowthW) w26 l27, []⟩,
            commitEnd, 0, [],
            [blockFrame Func14Proof.blockTwo [],
              blockFrame Func14Proof.blockOne epiloguePhase],
            callerFrame callerLocals stack code arity remainder controls ::
              calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  subst hmaskW
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, H0, H4, H8, H12, Hctrl, Hslots, Hk0,
    Hk1, Hbump, Hstreams, Hnormal⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  have hsz : UInt32.size = 4294967296 := rfl
  have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have ht0 := offset_facts table 0 0 rfl (by omega)
  have ht4 := offset_facts table 4 4 rfl (by omega)
  have ht8 := offset_facts table 8 8 rfl (by omega)
  rw [shape_commit_end]
  -- WAT 4085 to 4092: the three header writes
  ihave H0 := pointsTo_u32_at (UInt32.add_zero table) $$ H0
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := table) (offset := 4) oldHdrMask
    ht4.1 ht4.2.1 ht4.2.2.1 ht4.2.2.2 with H4
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := table) (offset := 0) oldCtrlW
    ht0.1 ht0.2.1 ht0.2.2.1 ht0.2.2.2 with H0
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_sub]
  rw [hgrowthW]
  wasm_twp_rebind twp_store32 (address := table) (offset := 8) oldHdrGrowth
    ht8.1 ht8.2.1 ht8.2.2.1 ht8.2.2.2 with H8
  -- WAT 4093 to 4094: the `Ok` tag
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  rw [show (2147483649 : UInt32) = okTag from rfl]
  -- the fresh table, as one predicate
  ihave H0 := pointsTo_u32_at (UInt32.add_zero table).symm $$ H0
  ihave Htable : HashMap.Table.TableAt 0 table
      (HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1) t 1)
      $$ [H0 H4 H8 H12 Hctrl Hslots]
  · rw [hres]
    isimp only [HashMap.Table.TableAt]
    iexists ctrlNew
    iright
    isplitl_pureexact hbuck
    isimp only [HashMap.Table.TableBody, HashMap.Table.tableHeader]
    isplitl_pureexact hroom
    isplitl [H0 H4 H8 H12]
    · isplitl_exact H0
      · isplitl_exact H4
        · isplitl_exact H8
          · irw_exact [hitems] with H12
    · isplitl_exact Hctrl
      · iexact Hslots
  iclose_map_runtime Hruntime with Hmodule Henv
  by_cases hsingle : t.buckets = 1
  · -- the old table is the static singleton, so the free is skipped
    have hmask0 : UInt32.ofNat (t.buckets - 1) = 0 := by
      rw [hsingle]
      rfl
    rw [hmask0]
    wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 1) (by rw [if_pos rfl])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply twp_exitControl (by rfl)
    simp only [List.take_zero, List.nil_append]
    iapply twp_resize_epilogue sp out table hasher p2 k0 k1 t outBefore
      below heapId storedCursor frontier history input output raised
      callerLocals stack code arity remainder controls calls s E Φ
      houtLength houtNowrap
    iframe Hruntime Hsp Hbelow Hout Htable Hk0 Hk1 Hbump Hstreams
    iexact Hnormal
  · -- the old table is allocated, so the free runs
    have hb4 : 4 ≤ t.buckets := by
      rcases hbShape with h | h
      · exact absurd h hsingle
      · exact h
    have hbwNat : (UInt32.ofNat t.buckets).toNat = t.buckets :=
      UInt32.toNat_ofNat_of_lt' (by omega)
    have hmwNat : (UInt32.ofNat (t.buckets - 1)).toNat = t.buckets - 1 :=
      UInt32.toNat_ofNat_of_lt' (by omega)
    have hmwNe : UInt32.ofNat (t.buckets - 1) ≠ 0 := by
      intro hzero
      rw [hzero] at hmwNat
      have : (0 : UInt32).toNat = 0 := rfl
      omega
    wasm_twp_pures [twp_localGet]
    iapply twp_eqz (result := 0) (by rw [if_neg hmwNe])
    iapply twp_brIfZero
    rw [shape_free_tail]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl]
    rw [show ((3 : UInt32) % 32) = 3 from by decide]
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_add twp_const twp_add]
    have hshlNat : ((UInt32.ofNat t.buckets) <<< (3 : UInt32)).toNat
        = t.buckets * 8 := by
      rw [toNat_shl3 (by rw [hbwNat]; omega), hbwNat]
    have hnw1 : ((UInt32.ofNat t.buckets) <<< (3 : UInt32)).toNat
        + (UInt32.ofNat (t.buckets - 1)).toNat < 4294967296 := by
      rw [hshlNat, hmwNat]
      omega
    have hsum1 : ((UInt32.ofNat t.buckets) <<< (3 : UInt32)
        + UInt32.ofNat (t.buckets - 1)).toNat
        = t.buckets * 8 + (t.buckets - 1) := by
      rw [toNat_add_nowrap hnw1, hshlNat, hmwNat]
    have h9 : (9 : UInt32).toNat = 9 := rfl
    have hnw2 : (9 : UInt32).toNat
        + ((UInt32.ofNat t.buckets) <<< (3 : UInt32)
          + UInt32.ofNat (t.buckets - 1)).toNat < 4294967296 := by
      rw [hsum1, h9]
      omega
    have hsum2 : ((9 : UInt32) + ((UInt32.ofNat t.buckets) <<< (3 : UInt32)
        + UInt32.ofNat (t.buckets - 1))).toNat = 9 * t.buckets + 8 := by
      rw [toNat_add_nowrap hnw2, hsum1, h9]
      omega
    have hz : (9 : UInt32) + ((UInt32.ofNat t.buckets) <<< (3 : UInt32)
        + UInt32.ofNat (t.buckets - 1)) ≠ 0 := by
      intro hzero
      rw [hzero] at hsum2
      have hz0 : (0 : UInt32).toNat = 0 := rfl
      omega
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply twp_eqz (result := 0) (by rw [if_neg hz])
    iapply twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_sub twp_localGet
      twp_const]
    have Hfree : DeallocNoop.Func57NoopSpec (hlc := hlc) :=
      DeallocNoop.func57_noop_correct
    unfold DeallocNoop.Func57NoopSpec CallContract callExpr at Hfree
    simp only [List.cons_append, List.nil_append] at Hfree
    iapply Hfree (stack := [])
      (callerLocals := ⟨[.i32 out, .i32 table,
          .i32 ((UInt32.ofNat t.buckets) <<< (3 : UInt32)), .i32 p3,
          .i32 okTag],
        rawLocals (.i32 (sp - 32)) (.i32 (UInt32.ofNat t.items))
          (.i32 ((9 : UInt32) + ((UInt32.ofNat t.buckets) <<< (3 : UInt32)
            + UInt32.ofNat (t.buckets - 1))))
          (.i32 (UInt32.ofNat t.buckets)) (.i32 ctrlNew) (.i32 ctrlOldPtr)
          (.i32 (UInt32.ofNat (n.buckets - 1))) l12 w13 w14 w15 w16 w17
          w18 w19 w20 w21 l22 l23 w24 (.i32 newGrowthW) w26 l27, []⟩)
    isplitl [Hruntime]
    · iexact Hruntime
    · unfold ResumeWP resumeExpr
      simp only [List.nil_append]
      iintro Hruntime
      iapply twp_exitControl (by rfl)
      simp only [List.take_zero, List.nil_append]
      iapply twp_exitControl (by rfl)
      simp only [List.take_zero, List.nil_append]
      iapply twp_resize_epilogue sp out table hasher
        ((UInt32.ofNat t.buckets) <<< (3 : UInt32)) k0 k1 t outBefore
        below heapId storedCursor frontier history input output raised
        callerLocals stack code arity remainder controls calls s E Φ
        houtLength houtNowrap
      iframe Hruntime Hsp Hbelow Hout Htable Hk0 Hk1 Hbump Hstreams
      iexact Hnormal

/-- The two physical forms of a table, as the four header words and the
memory that the walk reads.  The static singleton has no bucket area, and
it has no items, so the walk never runs on it. -/
theorem TableAt_open (base : UInt32) (t : HashMap.Table UInt32 UInt32)
    (hg : t.growthLeft = 0) :
    HashMap.Table.TableAt 0 base t ⊢
      iprop(∃ ctrl : UInt32,
        pointsTo_u32 0 base ctrl ∗
        pointsTo_u32 0 (base + 4) (UInt32.ofNat (t.buckets - 1)) ∗
        pointsTo_u32 0 (base + 8) 0 ∗
        pointsTo_u32 0 (base + 12) (UInt32.ofNat t.items) ∗
        (⌜t.items = 0⌝ ∨
          (⌜8 * t.buckets ≤ ctrl.toNat⌝ ∗
            Slices.ByteSlice 0 ctrl t.ctrl ∗
            HashMap.Table.slotsBefore 0 ctrl t.slots))) := by
  have hzero : UInt32.ofNat 0 = (0 : UInt32) := rfl
  iintro Htable
  isimp only [HashMap.Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Hbody⟩
  icases Hbody with (Hsingle | ⟨%hb, Hbody⟩)
  · isimp only [HashMap.Table.SingletonBody, HashMap.Table.tableHeader]
      at Hsingle
    icases Hsingle with ⟨%hsing, ⟨Hh0, Hh4, Hh8, Hh12⟩, Hctrl⟩
    obtain ⟨hb1, hi0, -⟩ := hsing
    iexists ctrl
    rw [hb1, hi0, show (1 : Nat) - 1 = 0 from rfl, hzero]
    isplitl_exact Hh0
    · isplitl_exact Hh4
      · isplitl_exact Hh8
        · isplitl_exact Hh12
          · ileft
            ipureintro
            rfl
  · isimp only [HashMap.Table.TableBody, HashMap.Table.tableHeader] at Hbody
    icases Hbody with ⟨%hroom, ⟨Hh0, Hh4, Hh8, Hh12⟩, Hctrl, Hslots⟩
    iexists ctrl
    isimp only [hg, hzero] at Hh8
    isplitl_exact Hh0
    · isplitl_exact Hh4
      · isplitl_exact Hh8
        · isplitl_exact Hh12
          · iright
            isplitl_pureexact hroom
            iframe Hctrl Hslots

/-- The locals of absolute `func 17` at the allocation, WAT 3665, on the
resize path.  Phase A left the item count in local 6, the old mask in
local 7, the old bucket count in local 8, `full_cap + 1` in local 9 and
`full_cap` in local 10. -/
@[reducible] def resizeAllocLocals (out table buckets hasher frame items
    mask oldBuckets fullSucc fullCap : UInt32) : Locals :=
  { params := [.i32 out, .i32 table, .i32 buckets, .i32 hasher, .i32 1],
    locals := rawLocals (.i32 frame) (.i32 items) (.i32 mask)
      (.i32 oldBuckets) (.i32 fullSucc) (.i32 fullCap) (.i32 0) (.i32 0)
      (.i64 0) (.i64 0) (.i64 0) (.i64 0) (.i64 0) (.i64 0) (.i64 0)
      (.i64 0) (.i64 0) (.i32 0) (.i32 0) (.i64 0) (.i32 0) (.i64 0)
      (.i32 0),
    values := [] }

/-- The locals at the two calls of WAT 3681 to 3686 on the resize path. -/
@[reducible] def resizeCallLocals (out table buckets hasher frame items
    mask oldBuckets fullCap total slots ctrlSize : UInt32) : Locals :=
  { params := [.i32 out, .i32 table, .i32 buckets, .i32 hasher, .i32 1],
    locals := rawLocals (.i32 frame) (.i32 items) (.i32 mask)
      (.i32 oldBuckets) (.i32 total) (.i32 fullCap) (.i32 slots)
      (.i32 ctrlSize) (.i64 0) (.i64 0) (.i64 0) (.i64 0) (.i64 0)
      (.i64 0) (.i64 0) (.i64 0) (.i64 0) (.i32 0) (.i32 0) (.i64 0)
      (.i32 0) (.i64 0) (.i32 0),
    values := [] }

set_option maxHeartbeats 8000000 in
/-- WAT 3665 to 4129: the allocation, the control fill, the walk and the
tail.  Both capacity branches of phase A end here with the same locals. -/
theorem twp_resize_commit
    (sp out table hasher bucketsWord ctrlOld : UInt32)
    (k0 k1 : UInt64) (t : HashMap.Table UInt32 UInt32)
    (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (houtLength : outBefore.length = 8)
    (houtNowrap : out.toNat + 8 < UInt32.size)
    (htableNowrap : table.toNat + 16 < UInt32.size)
    (hwf : HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t)
    (hcl : HashMap.Table.Clean t) (hg : t.growthLeft = 0)
    (hmax : t.items + 1 ≤ maxTableCapacity)
    (hhasherNowrap : hasher.toNat + 16 < UInt32.size)
    (hbuckets : bucketsWord.toNat
      = HashMap.Table.capacityToBuckets (ResizePures.resizeCap t)) :
    iprop(RuntimeContext ∗
      StackPointer (sp - 32) ∗
      StackBelow sp resizeDepth below ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 table ctrlOld ∗
      pointsTo_u32 0 (table + 4) (UInt32.ofNat (t.buckets - 1)) ∗
      pointsTo_u32 0 (table + 8) 0 ∗
      pointsTo_u32 0 (table + 12) (UInt32.ofNat t.items) ∗
      (⌜t.items = 0⌝ ∨
        (⌜8 * t.buckets ≤ ctrlOld.toNat⌝ ∗
          Slices.ByteSlice 0 ctrlOld t.ctrl ∗
          HashMap.Table.slotsBefore 0 ctrlOld t.slots)) ∗
      pointsTo_u64 0 hasher k0 ∗
      pointsTo_u64 0 (hasher + 8) k1 ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      (NormalArm sp out table hasher k0 k1 t heapId input output raised
          callerLocals stack code arity remainder controls calls s E Φ ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (Expr.running
          ⟨resizeAllocLocals out table bucketsWord hasher (sp - 32)
              (UInt32.ofNat t.items) (UInt32.ofNat (t.buckets - 1))
              (UInt32.ofNat t.buckets)
              (UInt32.ofNat (t.items + 1)) (UInt32.ofNat t.items),
            allocPhase, 0, [],
            [blockFrame blockFour overflowTailB,
              blockFrame blockThree commitTail,
              blockFrame Func14Proof.blockTwo [],
              blockFrame Func14Proof.blockOne epiloguePhase],
            callerFrame callerLocals stack code arity remainder controls ::
              calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, H0, H4, H8, H12, Hold, Hk0, Hk1,
    Hbump, Hstreams, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  have hsz : UInt32.size = 4294967296 := rfl
  have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have h29 : (2 : Nat) ^ 29 = 536870912 := by norm_num
  obtain ⟨haHigh, haLow⟩ := ResizePures.resize_buckets_bound hcl hg hmax
  have hBfour : 4 ≤ bucketsWord.toNat := by
    rw [hbuckets]; exact buckets_ge_four haLow haHigh
  have hBle : bucketsWord.toNat ≤ 2 ^ 27 := by
    rw [hbuckets]; exact buckets_le haHigh
  have hctrlNat : ((8 : UInt32) + bucketsWord).toNat
      = bucketsWord.toNat + 8 := by
    rw [UInt32.add_comm]
    exact toNat_add_lit (x := bucketsWord) (k := 8) (by omega)
  have hshlNat : (bucketsWord <<< (3 : UInt32)).toNat
      = bucketsWord.toNat * 8 := toNat_shl3 (by omega)
  have htotalNat :
      (bucketsWord <<< (3 : UInt32) + ((8 : UInt32) + bucketsWord)).toNat
        = bucketsWord.toNat * 8 + (bucketsWord.toNat + 8) := by
    rw [toNat_add_nowrap (by rw [hshlNat, hctrlNat]; omega), hshlNat,
      hctrlNat]
  -- WAT 3665 to 3672: `total = 8 * buckets + (buckets + 8)`
  wasm_twp_pures [twp_localGet twp_const twp_add]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const twp_shl]
  rw [show ((3 : UInt32) % 32) = 3 from by decide]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_add]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- WAT 3673 to 3675: the wrap guard of the sum
  wasm_twp_pures [twp_localGet]
  iapply twp_ltU (result := 0) (by
    rw [if_neg (by
      intro hlt
      have h := UInt32.lt_iff_toNat_lt.mp hlt
      rw [htotalNat, hctrlNat] at h
      omega)])
  iapply twp_brIfZero
  -- WAT 3676 to 3681: the size guard
  wasm_twp_pures [twp_localGet twp_const]
  iapply twp_gtU (result := 0) (by
    rw [if_neg (by
      intro hgt
      have h := UInt32.lt_iff_toNat_lt.mp hgt
      have hlit : (2147483640 : UInt32).toNat = 2147483640 := rfl
      rw [htotalNat] at h
      omega)])
  iapply twp_brIfZero
  -- WAT 3682: `call 33`, the empty allocation marker
  have Hmark : Func30Spec (hlc := hlc) :=
    Project.RustHashMap.Func30Proof.func30_correct
  unfold Func30Spec CallContract callExpr at Hmark
  simp only [List.nil_append] at Hmark
  iapply Hmark
    (callerLocals := resizeCallLocals out table bucketsWord hasher (sp - 32)
      (UInt32.ofNat t.items) (UInt32.ofNat (t.buckets - 1))
      (UInt32.ofNat t.buckets) (UInt32.ofNat t.items)
      (bucketsWord <<< 3 + ((8 : UInt32) + bucketsWord))
      (bucketsWord <<< 3) ((8 : UInt32) + bucketsWord))
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  · unfold ResumeWP resumeExpr
    simp only [List.nil_append]
    iintro Hruntime
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    -- WAT 3683 to 3686: `call 58` at alignment 8
    wasm_twp_pures [twp_localGet twp_const]
    have Halloc : Func55SpecPow2 (hlc := hlc) :=
      Project.RustHashMap.Func55Proof.func55_correct_pow2
    unfold Func55SpecPow2 CallContract callExpr at Halloc
    simp only [List.cons_append, List.nil_append] at Halloc
    iapply Halloc
      (size := bucketsWord <<< 3 + ((8 : UInt32) + bucketsWord))
      (alignment := 8) (layout := resizeLayout bucketsWord.toNat)
      (heapId := heapId) (storedCursor := storedCursor)
      (frontier := frontier) (history := history) (input := input)
      (output := output) (raised := raised)
      (callerLocals := resizeCallLocals out table bucketsWord hasher
        (sp - 32) (UInt32.ofNat t.items) (UInt32.ofNat (t.buckets - 1))
        (UInt32.ofNat t.buckets) (UInt32.ofNat t.items)
        (bucketsWord <<< 3 + ((8 : UInt32) + bucketsWord))
        (bucketsWord <<< 3) ((8 : UInt32) + bucketsWord))
      (stack := [])
    isplitl [Hmodule Henv]
    · unfold RuntimeContext
      iframe Hmodule Henv
    isplitl_exacts [Hbump Hstreams]
    isplitl_pureexact
      ⟨⟨by rw [htotalNat, resizeLayout_size]; omega, rfl⟩,
        resizeLayout_valid (by omega)⟩
    unfold AllocContinuation
    cases hdecision :
        classifyBump frontier (resizeLayout bucketsWord.toNat) with
    | oom =>
        iintro Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        iapply Hoom $$ %input Hstreams
    | success allocBase finish =>
        isplit
        · iintro %allocBytes Hruntime Hbump Hblock Hstreams
          iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
          isimp only [ResumeWP, resumeExpr, List.nil_append]
          simp only [List.cons_append, List.nil_append]
          ihave ⟨Htoken, Hbytes, %hblockFacts⟩ :=
            (LiveBlock_open heapId history.nextId allocBase
              (resizeLayout bucketsWord.toNat) allocBytes).mp $$ Hblock
          obtain ⟨hbytesLength, hbaseNonzero, hbaseAlign⟩ := hblockFacts
          isimp only [Slices.ByteSlice] at Hbytes
          icases Hbytes with ⟨%hallocBound, Hallocbytes⟩
          rw [hbytesLength, resizeLayout_size, hsz] at hallocBound
          ihave Hbytes : Slices.ByteSlice 0 allocBase allocBytes
              $$ [Hallocbytes]
          · isimp only [Slices.ByteSlice]
            isplitl_pureexact
              (by rw [hbytesLength, resizeLayout_size, hsz]; omega)
            iexact Hallocbytes
          wasm_twp_localTee [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          iapply twp_brIf hbaseNonzero (by rfl)
          simp only [List.take_zero, List.nil_append]
          rw [shape_commit_head]
          -- WAT 3716 to 3719: `new_ctrl = base + 8 * buckets`
          wasm_twp_pures [twp_localGet twp_localGet twp_add]
          wasm_twp_localSet [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          iapply twp_blockOf shape_fill
          have hdropLength :
              (allocBytes.drop (8 * bucketsWord.toNat)).length
                = bucketsWord.toNat + 8 := by
            rw [List.length_drop, hbytesLength, resizeLayout_size]
            omega
          have htakeLength :
              (allocBytes.take (8 * bucketsWord.toNat)).length
                = 8 * bucketsWord.toNat := by
            rw [List.length_take, hbytesLength, resizeLayout_size]
            omega
          have hofn8 :
              UInt32.ofNat (8 * bucketsWord.toNat) = bucketsWord <<< 3 := by
            apply UInt32.toNat_inj.mp
            rw [hshlNat, UInt32.toNat_ofNat_of_lt' (by omega)]
            omega
          have hctrlAddr : allocBase + UInt32.ofNat (8 * bucketsWord.toNat)
              = bucketsWord <<< 3 + allocBase := by
            rw [hofn8, UInt32.add_comm]
          ihave ⟨Hslots, Hctrl⟩ :=
            ByteSlice_cut allocBase allocBytes (8 * bucketsWord.toNat)
              (by rw [hbytesLength, resizeLayout_size]; omega) $$ Hbytes
          isimp only [hctrlAddr, Slices.ByteSlice] at Hctrl
          icases Hctrl with ⟨%hctrlBound, Hctrlbytes⟩
          rw [hdropLength, hsz] at hctrlBound
          -- WAT 3720 to 3722: the dead zero guard
          wasm_twp_pures [twp_localGet]
          iapply twp_eqz (result := 0) (by
            rw [if_neg (by
              intro hzero
              have hz : ((8 : UInt32) + bucketsWord).toNat = 0 := by
                rw [hzero]; rfl
              omega)])
          iapply twp_brIfZero
          -- WAT 3723 to 3728: the control fill
          wasm_twp_pures [twp_localGet twp_const twp_localGet]
          wasm_twp_bind twp_memoryFill32
            (allocBytes.drop (8 * bucketsWord.toNat))
            (by rw [hdropLength, hctrlNat]) (by rw [hctrlNat]; omega)
            (by rw [hctrlNat]; omega) with Hctrlbytes => Hctrlbytes
          iapply twp_exitControl (by rfl)
          simp only [List.take_zero, List.nil_append]
          rw [shape_commit_mid]
          -- WAT 3729 to 3742: the new growth counter
          have hmaskEq : (4294967295 : UInt32) + bucketsWord
              = UInt32.ofNat (bucketsWord.toNat - 1) := by
            apply UInt32.toNat_inj.mp
            rw [UInt32.add_comm, toNat_pred (by omega),
              UInt32.toNat_ofNat_of_lt' (by omega)]
          have ht0 := offset_facts table 0 0 rfl (by omega)
          wasm_twp_pures [twp_localGet twp_const twp_add]
          wasm_twp_localTee [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          rw [hmaskEq]
          wasm_twp_pures [twp_localGet twp_const twp_shrU]
          rw [show ((3 : UInt32) % 32) = 3 from by decide]
          wasm_twp_pures [twp_const twp_mul twp_localGet twp_const]
          iapply twp_ltU
            (result := if bucketsWord < (9 : UInt32) then (1 : UInt32)
              else 0) rfl
          iapply twp_select
            (selected := .i32 (UInt32.ofNat
              (HashMap.Table.bucketMaskToCapacity
                (bucketsWord.toNat - 1)))) (by
              have h9lit : (9 : UInt32).toNat = 9 := rfl
              by_cases h9 : bucketsWord < (9 : UInt32)
              · have h9n : bucketsWord.toNat < 9 := by
                  have h := UInt32.lt_iff_toNat_lt.mp h9
                  omega
                rw [if_pos h9, if_pos (by decide : (1 : UInt32) ≠ 0)]
                congr 1
                rw [← growthLeft_eq (b := bucketsWord.toNat) (by omega),
                  if_pos h9n]
              · have h9n : 9 ≤ bucketsWord.toNat := by
                  by_contra hc
                  exact h9 (UInt32.lt_iff_toNat_lt.mpr (by omega))
                rw [if_neg h9, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
                congr 1
                apply UInt32.toNat_inj.mp
                rw [← growthLeft_eq (b := bucketsWord.toNat) (by omega),
                  if_neg (by omega), UInt32.toNat_ofNat_of_lt' (by omega),
                  UInt32.toNat_mul, toNat_shr3,
                  show (7 : UInt32).toNat = 7 from rfl]
                omega)
          wasm_twp_localSet [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          -- WAT 3743 to 3745: the old control pointer
          ihave H0 := pointsTo_u32_at (UInt32.add_zero table) $$ H0
          wasm_twp_pures [twp_localGet]
          wasm_twp_rebind twp_load32 (address := table) (offset := 0)
            ctrlOld ht0.1 ht0.2.1 ht0.2.2.1 ht0.2.2.2 with H0
          wasm_twp_localSet [List.length_cons, List.length_nil,
            Nat.reduceAdd, Nat.reduceSub, List.set]
          ihave H0 := pointsTo_u32_at (UInt32.add_zero table).symm $$ H0
          iapply twp_blockOf shape_resize
          -- the fresh table, as the walk sees it before the first turn
          have hlayout : HashMap.Table.Layout
              (HashMap.SipHash.hashU32 k0 k1) t := hwf.toLayout
          have hbPos : 0 < t.buckets := hlayout.pos
          have hmaxEq : maxTableCapacity = 117440512 := rfl
          rw [hmaxEq] at hmax
          have hitemsNat : (UInt32.ofNat t.items).toNat = t.items :=
            UInt32.toNat_ofNat_of_lt' (by omega)
          have hfull := ResizePures.items_eq_fullCap hcl hg
          have hbHigh : t.buckets ≤ 2 ^ 27 := by
            unfold HashMap.Table.bucketMaskToCapacity at hfull
            by_cases hsm : t.buckets - 1 < 8
            · omega
            · rw [if_neg hsm] at hfull
              have hb1 : t.buckets - 1 + 1 = t.buckets := by omega
              rw [hb1] at hfull
              omega
          have hbSmall : t.buckets = 1 ∨ 4 ≤ t.buckets := by
            by_cases hlt : t.buckets < 8
            · rcases hlayout.shape.small hlt with h | h
              · exact Or.inl h
              · exact Or.inr (by omega)
            · exact Or.inr (by omega)
          obtain ⟨hwfN, hclN, hbN, hiN⟩ :=
            ResizePures.resize_spec hwf hcl hg (by rw [hmaxEq]; omega)
          have hnbuck : (HashMap.Table.reserve
              (HashMap.SipHash.hashU32 k0 k1) t 1).buckets
              = bucketsWord.toNat := by rw [hbN, ← hbuckets]
          have hcleanN := hclN.2
          rw [hnbuck, hiN] at hcleanN
          have hgrowthN : (HashMap.Table.reserve
              (HashMap.SipHash.hashU32 k0 k1) t 1).growthLeft
              = HashMap.Table.bucketMaskToCapacity (bucketsWord.toNat - 1)
                - t.items := by omega
          have hgcap : HashMap.Table.bucketMaskToCapacity
              (bucketsWord.toNat - 1) < 4294967296 := by
            unfold HashMap.Table.bucketMaskToCapacity
            by_cases hsm : bucketsWord.toNat - 1 < 8
            · rw [if_pos hsm]; omega
            · rw [if_neg hsm]; omega
          have hgrowthW : UInt32.ofNat (HashMap.Table.bucketMaskToCapacity
                (bucketsWord.toNat - 1)) - UInt32.ofNat t.items
              = UInt32.ofNat (HashMap.Table.reserve
                  (HashMap.SipHash.hashU32 k0 k1) t 1).growthLeft := by
            rw [hgrowthN, ofNat_sub_ofNat (by omega) (by omega)]
          have hnewCtrlNat : (bucketsWord <<< 3 + allocBase).toNat
              = bucketsWord.toNat * 8 + allocBase.toNat := by
            rw [toNat_add_nowrap (by rw [hshlNat]; omega), hshlNat]
          have hroomNew : 8 * (HashMap.Table.reserve
              (HashMap.SipHash.hashU32 k0 k1) t 1).buckets
              ≤ (bucketsWord <<< 3 + allocBase).toNat := by
            rw [hnbuck, hnewCtrlNat]
            omega
          have hfresh : walkTable (HashMap.SipHash.hashU32 k0 k1) t []
              = HashMap.Table.newEmpty bucketsWord.toNat := by
            show HashMap.Table.withCapacity (ResizePures.resizeCap t) = _
            rw [HashMap.Table.withCapacity_eq,
              ResizePures.capBuckets_resizeCap, hbuckets]
          isimp only [hdropLength, HashMap.Table.toUInt8_fillByte]
            at Hctrlbytes
          ihave HctrlNew : Slices.ByteSlice 0
              (bucketsWord <<< 3 + allocBase)
              (walkTable (HashMap.SipHash.hashU32 k0 k1) t []).ctrl
              $$ [Hctrlbytes]
          · rw [hfresh]
            isimp only [HashMap.Table.newEmpty, Slices.ByteSlice]
            isplitl_pureexact (by
              rw [List.length_replicate, hnewCtrlNat, hsz]
              omega)
            iexact Hctrlbytes
          ihave HslotsNew :=
            HashMap.Table.slotsBefore_replicate_none 0 bucketsWord.toNat
              allocBase (allocBytes.take (8 * bucketsWord.toNat))
              htakeLength $$ Hslots
          isimp only [hctrlAddr] at HslotsNew
          ihave HslotsNew : HashMap.Table.slotsBefore 0
              (bucketsWord <<< 3 + allocBase)
              (walkTable (HashMap.SipHash.hashU32 k0 k1) t []).slots
              $$ [HslotsNew]
          · rw [hfresh]
            isimp only [HashMap.Table.newEmpty]
            iexact HslotsNew
          have hresF : HashMap.Table.reserve
              (HashMap.SipHash.hashU32 k0 k1) t 1
              = HashMap.Table.withCounters
                  (walkTable (HashMap.SipHash.hashU32 k0 k1) t
                    (HashMap.Table.fullIndices t)) t.items
                  ((walkTable (HashMap.SipHash.hashU32 k0 k1) t
                    (HashMap.Table.fullIndices t)).growthLeft - t.items) :=
            ResizePures.reserve_one_fields hcl hg
          have hbuckN : 1 < (HashMap.Table.reserve
              (HashMap.SipHash.hashU32 k0 k1) t 1).buckets := by
            rw [hnbuck]; omega
          ihave Hnormal := BI.and_elim_l $$ Hcont
          -- WAT 3747 to 3749: the walk runs only when the table has items
          by_cases hzero : t.items = 0
          · -- no items, so the fresh table is already the answer
            have h0nat : (0 : UInt32).toNat = 0 := rfl
            have h60 : UInt32.ofNat t.items = 0 := by
              apply UInt32.toNat_inj.mp
              rw [hitemsNat, h0nat, hzero]
            have hnil : HashMap.Table.fullIndices t = [] := by
              have hlen := HashMap.Table.length_fullIndices hlayout
              rw [← hwf.items_eq, hzero] at hlen
              exact List.eq_nil_of_length_eq_zero hlen
            wasm_twp_pures [twp_localGet]
            iapply twp_eqz (result := 1) (by rw [if_pos h60])
            iapply twp_brIf (by decide) (by rfl)
            simp only [List.take_zero, List.nil_append]
            ihave HctrlFin : Slices.ByteSlice 0
                (bucketsWord <<< 3 + allocBase)
                (HashMap.Table.reserve
                  (HashMap.SipHash.hashU32 k0 k1) t 1).ctrl $$ [HctrlNew]
            · rw [hresF, hnil, withCounters_ctrl]
              iexact HctrlNew
            ihave HslotsFin : HashMap.Table.slotsBefore 0
                (bucketsWord <<< 3 + allocBase)
                (HashMap.Table.reserve
                  (HashMap.SipHash.hashU32 k0 k1) t 1).slots $$ [HslotsNew]
            · rw [hresF, hnil, withCounters_slots]
              iexact HslotsNew
            iclose_map_runtime Hruntime with Hmodule Henv
            iapply (twp_resize_tail (t := t)
              (n := HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1)
                t 1)
              (hmaskW := by rw [hnbuck]) (houtLength := houtLength)
              (houtNowrap := houtNowrap) (htableNowrap := htableNowrap)
              (hbPos := hbPos) (hbHigh := hbHigh) (hbShape := hbSmall)
              (hitems := hiN) (hroom := hroomNew) (hbuck := hbuckN)
              (hgrowthW := hgrowthW) (hres := rfl))
            iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 HctrlFin HslotsFin
              Hk0 Hk1 Hbump Hstreams
            iexact Hnormal
          · -- the old table has items, so the walk runs
            have hone : 1 ≤ t.items := by omega
            have h0nat : (0 : UInt32).toNat = 0 := rfl
            have h60 : UInt32.ofNat t.items ≠ 0 := by
              intro hzz
              rw [hzz, h0nat] at hitemsNat
              exact hzero hitemsNat.symm
            wasm_twp_pures [twp_localGet]
            iapply twp_eqz (result := 0) (by rw [if_neg h60])
            iapply twp_brIfZero
            rw [resize_tail_eq, shape_resize_tail]
            icases Hold with (%hz | ⟨%hroomOld, HctrlOld, HslotsOld⟩)
            · exact absurd hz hzero
            ihave ⟨%hg8, Hgroup, Hback⟩ :=
              Func15Insert.group0_focus ctrlOld t
                (by rw [hlayout.ctrl_len]; omega) $$ HctrlOld
            ihave Hgroup := wordMove64 (UInt32.add_zero ctrlOld).symm
              $$ Hgroup
            iapply (twp_resize_hoist (g := HashMap.Table.groupWord
                (HashMap.Table.groupAt t 0))
              (hhasher := by omega) (hctrlOld := by omega))
            isplitl_exacts [Hk0 Hk1 Hgroup]
            iintro %a14 %a15 %a16 Hk0 Hk1 Hgroup
            ihave Hgroup := wordMove64 (UInt32.add_zero ctrlOld) $$ Hgroup
            ihave HctrlOld := Hback $$ Hgroup
            obtain ⟨m, hm, -, hpow⟩ := hwfN.toLayout.shape
            have hcapB : HashMap.Table.capBuckets
                (ResizePures.resizeCap t) = bucketsWord.toNat := by
              rw [ResizePures.capBuckets_resizeCap, ← hbuckets]
            have hbShapeW : HashMap.Table.capBuckets
                (ResizePures.resizeCap t) = 2 ^ m := by
              rw [hcapB, ← hnbuck]
              exact hpow
            have hroomNewW : 8 * HashMap.Table.capBuckets
                (ResizePures.resizeCap t)
                ≤ (bucketsWord <<< 3 + allocBase).toNat := by
              rw [hcapB, hnewCtrlNat]
              omega
            have Hwalk := twp_resize_walk (hlc := hlc) t k0 k1
              (HashMap.SipHash.hashU32 k0 k1) rfl hwf hcl hg
              (by rw [hmaxEq]; omega) hone m hm hbShapeW
              (bucketsWord <<< 3 + allocBase) ctrlOld hroomNewW hroomOld
              (hoistWasm k0 k1) (hoistWasm_eq k0 k1) out table
              (.i32 (sp - 32)) (.i32 (UInt32.ofNat t.items))
              (.i32 (UInt32.ofNat (t.buckets - 1)))
              (.i32 (UInt32.ofNat t.buckets))
              (.i32 (UInt32.ofNat (HashMap.Table.bucketMaskToCapacity
                (bucketsWord.toNat - 1))))
              (.i32 ((8 : UInt32) + bucketsWord)) (.i64 a14) (.i64 a15)
              (.i64 a16) (.i64 0) (.i32 allocBase) (.i32 0) (.i64 0)
              (.i32 0) (contCode := []) (arity := 0) (remainder := [])
              (controls := [blockFrame Func14Proof.blockResize commitEnd,
                blockFrame Func14Proof.blockTwo [],
                blockFrame Func14Proof.blockOne epiloguePhase])
              (calls := callerFrame callerLocals stack code arity
                remainder controls :: calls)
              (s := s) (E := E) (Φ := Φ)
            rw [show UInt32.ofNat (8 * 0) = (0 : UInt32) from rfl,
              UInt32.add_zero, hcapB] at Hwalk
            iapply Hwalk $$ HctrlOld HslotsOld HctrlNew HslotsNew
            iintro %v2 %v4 %v12 %v13 %v14 %v15 %v16 %v17 %v22 %v23 %v24
              %v27 HctrlOld HslotsOld HctrlFinW HslotsFinW
            iapply twp_exitControl (by rfl)
            simp only [List.take_zero, List.nil_append]
            ihave HctrlFin : Slices.ByteSlice 0
                (bucketsWord <<< 3 + allocBase)
                (HashMap.Table.reserve
                  (HashMap.SipHash.hashU32 k0 k1) t 1).ctrl
                $$ [HctrlFinW]
            · rw [hresF, withCounters_ctrl]
              iexact HctrlFinW
            ihave HslotsFin : HashMap.Table.slotsBefore 0
                (bucketsWord <<< 3 + allocBase)
                (HashMap.Table.reserve
                  (HashMap.SipHash.hashU32 k0 k1) t 1).slots
                $$ [HslotsFinW]
            · rw [hresF, withCounters_slots]
              iexact HslotsFinW
            iclose_map_runtime Hruntime with Hmodule Henv
            iapply (twp_resize_tail (t := t)
              (n := HashMap.Table.reserve (HashMap.SipHash.hashU32 k0 k1)
                t 1)
              (hmaskW := by rw [hnbuck]) (houtLength := houtLength)
              (houtNowrap := houtNowrap) (htableNowrap := htableNowrap)
              (hbPos := hbPos) (hbHigh := hbHigh) (hbShape := hbSmall)
              (hitems := hiN) (hroom := hroomNew) (hbuck := hbuckN)
              (hgrowthW := hgrowthW) (hres := rfl))
            iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 HctrlFin HslotsFin
              Hk0 Hk1 Hbump Hstreams
            iexact Hnormal
        · iintro Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          iapply Hoom $$ %input Hstreams

set_option maxHeartbeats 4000000 in
/-- Absolute `func 17` on the path that absolute `func 18` takes: a
general old table with no growth left, and one more item. -/
theorem func14_resize_correct : Func14ResizeSpec (hlc := hlc) := by
  unfold Func14ResizeSpec CallContract callExpr
  intro sp out table hasher k0 k1 t outBefore below heapId storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Htable, Hk0, Hk1, Hbump, Hstreams,
    %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, htableNowrap, hhasherNowrap,
    hwf, hcl, hg, hmax⟩ := hfacts
  have hsz : UInt32.size = 4294967296 := rfl
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  have hlayout : HashMap.Table.Layout
    (HashMap.SipHash.hashU32 k0 k1) t := hwf.toLayout
  have hbPos : 0 < t.buckets := hlayout.pos
  have hfull := ResizePures.items_eq_fullCap hcl hg
  have hcapVal : ResizePures.resizeCap t = t.items + 1 :=
    ResizePures.resizeCap_eq_items_succ hcl hg
  rw [hmaxEq] at hmax
  have hitemsNat : (UInt32.ofNat t.items).toNat = t.items :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hsucNat : (UInt32.ofNat (t.items + 1)).toNat = t.items + 1 :=
    UInt32.toNat_ofNat_of_lt' (by omega)
  have hbHigh : t.buckets ≤ 2 ^ 27 := by
    have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
    unfold HashMap.Table.bucketMaskToCapacity at hfull
    by_cases hsm : t.buckets - 1 < 8
    · omega
    · rw [if_neg hsm] at hfull
      have hb1 : t.buckets - 1 + 1 = t.buckets := by omega
      rw [hb1] at hfull
      omega
  have hmaskNat : (UInt32.ofNat (t.buckets - 1)).toNat = t.buckets - 1 := by
    have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
    exact UInt32.toNat_ofNat_of_lt' (by omega)
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 17
      Project.RustHashMap.func14Def (by decide) func14_index with Hmodule
  simp [Project.RustHashMap.func14Def, Function.toLocals,
    Function.numParams, ValueType.zero]
  rw [func14_shape]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  iapply twp_blockOf shape_one
  iapply twp_blockOf shape_two
  iapply twp_blockOf shape_three
  iapply twp_blockOf shape_four
  iapply twp_blockOf shape_five
  iapply twp_blockOf shape_six
  iapply twp_blockOf shape_seven
  ihave ⟨%ctrlOld, H0, H4, H8, H12, Hold⟩ := TableAt_open table t hg
    $$ Htable
  have ht4 := offset_facts table 4 4 rfl (by omega)
  have ht12 := offset_facts table 12 12 rfl (by omega)
  -- WAT 3027 to 3041: `new_items = items + 1`, which never wraps
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := table) (offset := 12)
    (UInt32.ofNat t.items) ht12.1 ht12.2.1 ht12.2.2.1 ht12.2.2.2 with H12
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_add]
  rw [Func15Insert.oneAddOfNat t.items]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_ltU (result := 0) (by
    rw [if_neg (by
      intro hlt
      have h := UInt32.lt_iff_toNat_lt.mp hlt
      rw [hsucNat, hitemsNat] at h
      omega)])
  iapply twp_brIfZero
  iapply twp_blockOf shape_capacity
  have hbucketsNat : (UInt32.ofNat t.buckets).toNat = t.buckets := by
    have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
    exact UInt32.toNat_ofNat_of_lt' (by omega)
  have h8lit : (8 : UInt32).toNat = 8 := rfl
  -- WAT 3043 to 3060: `full_cap`
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := table) (offset := 4)
    (UInt32.ofNat (t.buckets - 1)) ht4.1 ht4.2.1 ht4.2.2.1 ht4.2.2.2
    with H4
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [Func15Insert.oneAddOfNat (t.buckets - 1),
    show t.buckets - 1 + 1 = t.buckets from by omega]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_shrU]
  rw [show ((3 : UInt32) % 32) = 3 from by decide]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_mul twp_localGet twp_const]
  iapply twp_ltU
    (result := if UInt32.ofNat (t.buckets - 1) < (8 : UInt32)
      then (1 : UInt32) else 0) rfl
  iapply twp_select (selected := .i32 (UInt32.ofNat t.items)) (by
    by_cases h8 : UInt32.ofNat (t.buckets - 1) < (8 : UInt32)
    · have h8n : t.buckets - 1 < 8 := by
        have h := UInt32.lt_iff_toNat_lt.mp h8
        rw [hmaskNat, h8lit] at h
        omega
      rw [if_pos h8, if_pos (by decide : (1 : UInt32) ≠ 0)]
      congr 1
      rw [hfull, ← growthLeft_eq (b := t.buckets) (by omega),
        if_pos (by omega)]
    · have h8n : 8 ≤ t.buckets - 1 := by
        by_contra hc
        have hlt : (UInt32.ofNat (t.buckets - 1)).toNat
            < (8 : UInt32).toNat := by
          rw [hmaskNat, h8lit]
          omega
        exact h8 (UInt32.lt_iff_toNat_lt.mpr hlt)
      rw [if_neg h8, if_neg (by decide : ¬ ((0 : UInt32) ≠ 0))]
      congr 1
      apply UInt32.toNat_inj.mp
      rw [hfull, ← growthLeft_eq (b := t.buckets) (by omega),
        if_neg (by omega), UInt32.toNat_ofNat_of_lt' (by omega),
        UInt32.toNat_mul, toNat_shr3,
        show (7 : UInt32).toNat = 7 from rfl, hbucketsNat]
      omega)
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- WAT 3063 to 3064: the rehash-in-place arm is dead
  wasm_twp_pures [twp_const twp_shrU]
  rw [show ((1 : UInt32) % 32) = 1 from by decide]
  have hshr1 : (UInt32.ofNat t.items >>> (1 : UInt32)).toNat
      = t.items / 2 := by
    rw [UInt32.toNat_shiftRight,
      show UInt32.toNat 1 % 32 = 1 from by decide,
      Nat.shiftRight_eq_div_pow, hitemsNat]
  iapply twp_leU (result := 0) (by
    rw [if_neg (by
      intro hle
      have h := UInt32.le_iff_toNat_le.mp hle
      rw [hsucNat, hshr1] at h
      omega)])
  iapply twp_brIfZero
  -- WAT 3065 to 3077: `cap = max (new_items, full_cap + 1)`
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [Func15Insert.oneAddOfNat t.items]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_gtU (result := 0) (by
    rw [if_neg (by
      intro hgt
      have h := UInt32.lt_iff_toNat_lt.mp hgt
      omega)])
  iapply twp_select (selected := .i32 (UInt32.ofNat (t.items + 1)))
    (by rw [if_neg (by decide)])
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  have hcapLow : 1 ≤ (UInt32.ofNat (t.items + 1)).toNat := by
    rw [hsucNat]
    omega
  have hcapHigh : (UInt32.ofNat (t.items + 1)).toNat
      ≤ maxTableCapacity := by
    rw [hsucNat, hmaxEq]
    omega
  have hcapNat : ResizePures.resizeCap t
      = (UInt32.ofNat (t.items + 1)).toNat := by
    rw [hcapVal, hsucNat]
  have h4nat : (4 : UInt32).toNat = 4 := rfl
  have h15nat : (15 : UInt32).toNat = 15 := rfl
  by_cases hsmall : UInt32.ofNat (t.items + 1) < 15
  · -- WAT 3653 to 3663: fewer than fifteen entries
    have ha15 : (UInt32.ofNat (t.items + 1)).toNat < 15 := by
      have h := UInt32.lt_iff_toNat_lt.mp hsmall
      omega
    iapply twp_ltU (result := 1) (by rw [if_pos hsmall])
    iapply twp_brIf (by decide) (by rfl)
    wasm_twp_pures [twp_const twp_localGet twp_const twp_and twp_const
      twp_add twp_localGet twp_const]
    by_cases htiny : UInt32.ofNat (t.items + 1) < 4
    · -- three entries or fewer: four buckets
      have ha4 : (UInt32.ofNat (t.items + 1)).toNat < 4 := by
        have h := UInt32.lt_iff_toNat_lt.mp htiny
        omega
      have hbuck : (4 : UInt32).toNat
          = HashMap.Table.capacityToBuckets (ResizePures.resizeCap t) := by
        rw [hcapNat, h4nat, buckets_tiny hcapLow ha4]
      iapply twp_ltU (result := 1) (by rw [if_pos htiny])
      iapply twp_select (selected := .i32 4) (by rw [if_pos (by decide)])
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      iapply twp_exitControl (by rfl)
      simp only [List.take_zero, List.nil_append]
      iclose_map_runtime Hruntime with Hmodule Henv
      ihave Hsp : StackPointer (sp - 32) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      iapply twp_resize_commit sp out table hasher 4 ctrlOld k0 k1 t
        outBefore below heapId storedCursor frontier history input output
        raised callerLocals stack code arity remainder controls calls s E Φ
        houtLength houtNowrap htableNowrap hwf hcl hg
        (by rw [hmaxEq]; omega) hhasherNowrap hbuck
      iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 Hold Hk0 Hk1 Hbump
        Hstreams
      iexact Hcont
    · -- four to fourteen entries: eight or sixteen buckets
      have ha4 : 4 ≤ (UInt32.ofNat (t.items + 1)).toNat := by
        by_contra hcon
        exact htiny (UInt32.lt_iff_toNat_lt.mpr (by omega))
      have h8nat : (8 : UInt32).toNat = 8 := rfl
      have hand : ((UInt32.ofNat (t.items + 1)) &&& 8).toNat ≤ 8 := by
        rw [UInt32.toNat_and, h8nat]
        exact Nat.and_le_right
      have hbuck : ((8 : UInt32) + (UInt32.ofNat (t.items + 1) &&& 8)).toNat
          = HashMap.Table.capacityToBuckets (ResizePures.resizeCap t) := by
        have hadd : ((8 : UInt32)
            + (UInt32.ofNat (t.items + 1) &&& 8)).toNat
            = (UInt32.ofNat (t.items + 1) &&& 8).toNat + 8 := by
          rw [UInt32.add_comm]
          exact toNat_add_lit
            (x := UInt32.ofNat (t.items + 1) &&& 8) (k := 8) (by omega)
        rw [hcapNat, hadd, UInt32.toNat_and, h8nat]
        exact buckets_small ha4 ha15
      iapply twp_ltU (result := 0) (by rw [if_neg htiny])
      iapply twp_select
        (selected := .i32 ((8 : UInt32) + (UInt32.ofNat (t.items + 1) &&& 8)))
        (by rw [if_neg (by decide)])
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      iapply twp_exitControl (by rfl)
      simp only [List.take_zero, List.nil_append]
      iclose_map_runtime Hruntime with Hmodule Henv
      ihave Hsp : StackPointer (sp - 32) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      iapply twp_resize_commit sp out table hasher
        ((8 : UInt32) + (UInt32.ofNat (t.items + 1) &&& 8)) ctrlOld k0 k1 t
        outBefore below heapId storedCursor frontier history input output
        raised callerLocals stack code arity remainder controls calls s E Φ
        houtLength houtNowrap htableNowrap hwf hcl hg
        (by rw [hmaxEq]; omega) hhasherNowrap hbuck
      iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 Hold Hk0 Hk1 Hbump
        Hstreams
      iexact Hcont
  · -- WAT 3079 to 3100: fifteen entries or more
    have h29 : (2 : Nat) ^ 29 = 536870912 := by norm_num
    have haNum : (UInt32.ofNat (t.items + 1)).toNat ≤ 117440512 := by
      rw [hmaxEq] at hcapHigh
      exact hcapHigh
    have ha15 : 15 ≤ (UInt32.ofNat (t.items + 1)).toNat := by
      by_contra hcon
      exact hsmall (UInt32.lt_iff_toNat_lt.mpr (by omega))
    iapply twp_ltU (result := 0) (by rw [if_neg hsmall])
    iapply twp_brIfZero
    iapply twp_blockOf shape_clz
    wasm_twp_pures [twp_localGet twp_const]
    iapply twp_gtU (result := 0) (by
      rw [if_neg (by
        intro hgt
        have h := UInt32.lt_iff_toNat_lt.mp hgt
        have hlit : (536870911 : UInt32).toNat = 536870911 := rfl
        omega)])
    iapply twp_brIfZero
    wasm_twp_pures [twp_const twp_localGet twp_const twp_shl]
    rw [show ((3 : UInt32) % 32) = 3 from by decide]
    wasm_twp_pures [twp_const]
    iapply twp_divU (by decide)
    wasm_twp_pures [twp_const twp_add]
    iapply twp_clz
    wasm_twp_pures [twp_shrU]
    rw [shrU_mod]
    have hshl : (UInt32.ofNat (t.items + 1) <<< (3 : UInt32)).toNat
        = (UInt32.ofNat (t.items + 1)).toNat * 8 :=
      toNat_shl3 (by omega)
    have hq : ((UInt32.ofNat (t.items + 1) <<< (3 : UInt32)) / 7).toNat
        = (UInt32.ofNat (t.items + 1)).toNat * 8 / 7 := by
      rw [UInt32.toNat_div, hshl, show (7 : UInt32).toNat = 7 from rfl]
    have hofn : (4294967295 : UInt32)
        + ((UInt32.ofNat (t.items + 1) <<< (3 : UInt32)) / 7)
        = UInt32.ofNat ((UInt32.ofNat (t.items + 1)).toNat * 8 / 7 - 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.add_comm, toNat_pred (by rw [hq]; omega), hq]
      exact (UInt32.toNat_ofNat_of_lt' (by omega)).symm
    rw [hofn]
    set tWord : UInt32 := (0xFFFFFFFF : UInt32) >>>
      UInt32.ofNat (clz32 32 (UInt32.ofNat
        ((UInt32.ofNat (t.items + 1)).toNat * 8 / 7 - 1)))
      with htdef
    have hbig : tWord.toNat + 1
        = HashMap.Table.capacityToBuckets
            (UInt32.ofNat (t.items + 1)).toNat := by
      rw [htdef]
      exact buckets_big ha15 (by rw [hmaxEq]; exact haNum)
    have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
    have htle : tWord.toNat + 1 ≤ 2 ^ 27 := by
      rw [hbig]
      exact buckets_le (by rw [hmaxEq]; exact haNum)
    have hadd1 : (tWord + (1 : UInt32)).toNat = tWord.toNat + 1 :=
      toNat_add_lit (x := tWord) (k := 1) (by omega)
    have hbuck : ((1 : UInt32) + tWord).toNat
        = HashMap.Table.capacityToBuckets (ResizePures.resizeCap t) := by
      rw [hcapNat, UInt32.add_comm, hadd1]
      exact hbig
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    iapply twp_gtU (result := 0) (by
      rw [if_neg (by
        intro hgt
        have h := UInt32.lt_iff_toNat_lt.mp hgt
        have hlit : (536870910 : UInt32).toNat = 536870910 := rfl
        omega)])
    iapply twp_brIfZero
    wasm_twp_pures [twp_localGet twp_const twp_add]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    iapply twp_br (by rfl)
    dsimp only
    simp only [List.take_zero, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hsp : StackPointer (sp - 32) $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iapply twp_resize_commit sp out table hasher ((1 : UInt32) + tWord)
      ctrlOld k0 k1 t outBefore below heapId storedCursor frontier history
      input output raised callerLocals stack code arity remainder controls
      calls s E Φ houtLength houtNowrap htableNowrap hwf hcl hg
      (by rw [hmaxEq]; omega) hhasherNowrap hbuck
    iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 Hold Hk0 Hk1 Hbump
      Hstreams
    iexact Hcont

end Project.RustHashMap.Func14Resize
