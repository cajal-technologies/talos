import Project.RustHashMap.Func14Capacity
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func30Proof
import CodeLib.RustStd.HashMap.FreshTable

/-!
# Proof of the reserve of `collect_entries`

This file proves local `func14`, absolute index 17, WAT lines 3019 to
4130.  It is `RawTableInner::reserve_rehash_inner`.

`collect_entries` calls it once, on the static empty table, so `items` is
0 and `bucket_mask` is 0.  Three large regions are dead on that path: the
rehash-in-place arm at WAT 3116 to 3640, the resize walk at WAT 3746 to
4084, and the free of the old control array at WAT 4098 to 4117.  About
130 of the 1112 lines run.

`func14_correct_of` takes `AllocatorContracts.Func55SpecPow2` as a
hypothesis, because the body allocates at alignment 8 and `Func55Spec`
covers alignment 1 and alignment 4 only.
`Project.RustHashMap.Func55Proof.func55_correct_pow2` proves that
contract.  This file does not import `Func55Proof.lean`, so the caller
supplies it.
-/

namespace Project.RustHashMap.Func14Proof

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.VecGrow
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.Func14Capacity
open scoped Wasm.SmallStep.Outcome

/-! ## The control blocks of the body

The body is a nest of seven blocks with three more inside it.  Only about
130 of its 1112 WAT lines run on the collect path, so the dead regions get
no name of their own: `blockAt` reads a block body straight off the
compiled program, and every shape theorem below closes by `rfl`. -/

/-- The body of the `block` instruction at index `i` of `p`. -/
private def blockAt (p : Program) (i : Nat) : Program :=
  match p[i]? with
  | some (.block _ _ body) => body
  | _ => []

private def blockOne : Program := blockAt Project.RustHashMap.func14 5
private def blockTwo : Program := blockAt blockOne 0
private def blockThree : Program := blockAt blockTwo 0
private def blockFour : Program := blockAt blockThree 0
private def blockFive : Program := blockAt blockFour 0
private def blockSix : Program := blockAt blockFive 0
private def blockSeven : Program := blockAt blockSix 0
private def blockCapacity : Program := blockAt blockSeven 9
private def blockClz : Program := blockAt blockCapacity 35
private def commitTail : Program := blockTwo.drop 1
private def blockFill : Program := blockAt commitTail 4
private def commitMid : Program := commitTail.drop 5
private def blockResize : Program := blockAt commitMid 17
private def commitEnd : Program := commitMid.drop 18

/-- The dead tail of block seven: `rehash_in_place`, WAT 3116 to 3640. -/
private def rehashTail : Program := blockSeven.drop 10

/-- The dead capacity-overflow arms, WAT 3101 to 3113, 3642 to 3651 and
3703 to 3713. -/
private def overflowTailC : Program := blockCapacity.drop 36
private def overflowTailA : Program := blockSix.drop 1
private def overflowTailB : Program := blockThree.drop 1

/-- The dead resize walk, WAT 3750 to 4084, and the dead free of the static
singleton, WAT 4098 to 4117. -/
private def resizeTail : Program := blockResize.drop 3
private def freeTail : Program := commitEnd.drop 16

/-! ## The live phases -/

/-- WAT 3021 to 3025: the 32-byte frame. -/
@[reducible] private def framePhase (contCode : Program) : Program :=
  .globalGet 0 :: .const 32 :: .sub :: .localTee 5 :: .globalSet 0 :: contCode

/-- WAT 4119 to 4129: the result slot and the stack pointer. -/
@[reducible] private def epiloguePhase : Program :=
  [.localGet 0, .localGet 2, .store32 4, .localGet 0, .localGet 4,
    .store32 0, .localGet 5, .const 32, .add, .globalSet 0]

/-- WAT 3027 to 3041: `new_items = items + additional` and the wrap guard. -/
@[reducible] private def itemsPhase (contCode : Program) : Program :=
  .localGet 1 :: .load32 12 :: .localTee 6 :: .localGet 2 :: .add ::
    .localTee 2 :: .localGet 6 :: .ltU :: .br_if 0 :: contCode

/-- WAT 3043 to 3077: the full capacity, the rehash test and
`cap = max(new_items, full_cap + 1)`. -/
@[reducible] private def capacityPhase (contCode : Program) : Program :=
  .localGet 2 :: .localGet 1 :: .load32 4 :: .localTee 7 ::
    .localGet 7 :: .const 1 :: .add :: .localTee 8 :: .const 3 :: .shrU ::
    .localTee 9 :: .const 7 :: .mul :: .localGet 7 :: .const 8 ::
    .ltU :: .select :: .localTee 10 :: .const 1 :: .shrU :: .leU ::
    .br_if 0 :: .localGet 10 :: .const 1 :: .add :: .localTee 9 ::
    .localGet 2 :: .localGet 9 :: .localGet 2 :: .gtU :: .select ::
    .localTee 2 :: .const 15 :: .ltU :: .br_if 2 :: contCode

/-- WAT 3079 to 3100: `buckets = (0xFFFFFFFF >>> clz (cap * 8 / 7 - 1)) + 1`. -/
@[reducible] private def clzPhase : Program :=
  [.localGet 2, .const 536870911, .gtU, .br_if 0, .const 4294967295,
    .localGet 2, .const 3, .shl, .const 7, .divU, .const 4294967295,
    .add, .clz, .shrU, .localTee 2, .const 536870910, .gtU, .br_if 5,
    .localGet 2, .const 1, .add, .localSet 2, .br 4]

/-- WAT 3653 to 3663: `buckets = if cap < 4 then 4 else (cap &&& 8) + 8`. -/
@[reducible] private def smallPhase : Program :=
  [.const 4, .localGet 2, .const 8, .and, .const 8, .add, .localGet 2,
    .const 4, .ltU, .select, .localSet 2]

/-- WAT 3665 to 3701: the two allocation guards, the allocation itself and
the dead null arm. -/
@[reducible] private def allocPhase : Program :=
  [.localGet 2, .const 8, .add, .localTee 12, .localGet 2, .const 3,
    .shl, .localTee 11, .add, .localTee 9, .localGet 12, .ltU, .br_if 0,
    .localGet 9, .const 2147483640, .gtU, .br_if 0, .call 33,
    .localGet 9, .const 8, .call 58, .localTee 22, .br_if 1,
    .localGet 5, .const 16, .add, .localGet 4, .const 8, .localGet 9,
    .call 98, .localGet 5, .load32 20, .localSet 2, .localGet 5,
    .load32 16, .localSet 4, .br 3]

/-- WAT 3716 to 3719: `new_ctrl = base + 8 * buckets`. -/
@[reducible] private def commitHead (contCode : Program) : Program :=
  .localGet 22 :: .localGet 11 :: .add :: .localSet 9 :: contCode

/-- WAT 3720 to 3728: the guarded `memory.fill` of the control bytes. -/
@[reducible] private def fillPhase : Program :=
  [.localGet 12, .eqz, .br_if 0, .localGet 9, .const 255, .localGet 12,
    .memoryFill]

/-- WAT 3729 to 3745: the new growth counter and the old control pointer. -/
@[reducible] private def fullCapPhase (contCode : Program) : Program :=
  .localGet 2 :: .const 4294967295 :: .add :: .localTee 11 ::
    .localGet 2 :: .const 3 :: .shrU :: .const 7 :: .mul :: .localGet 2 ::
    .const 9 :: .ltU :: .select :: .localSet 25 :: .localGet 1 ::
    .load32 0 :: .localSet 10 :: contCode

/-- WAT 4085 to 4097: the three header writes, the `Ok` tag and the guard
of the dead free. -/
@[reducible] private def storePhase (contCode : Program) : Program :=
  .localGet 1 :: .localGet 11 :: .store32 4 :: .localGet 1 ::
    .localGet 9 :: .store32 0 :: .localGet 1 :: .localGet 25 ::
    .localGet 6 :: .sub :: .store32 8 :: .const 2147483649 ::
    .localSet 4 :: .localGet 7 :: .eqz :: .br_if 0 :: contCode

/-! ## The split, closed by `rfl` -/

private theorem func14_shape :
    Project.RustHashMap.func14
      = framePhase (.block 0 0 blockOne :: epiloguePhase) := by rfl

private theorem shape_one : blockOne = [.block 0 0 blockTwo] := by rfl

private theorem shape_two : blockTwo = .block 0 0 blockThree :: commitTail := by rfl

private theorem shape_three :
    blockThree = .block 0 0 blockFour :: overflowTailB := by rfl

private theorem shape_four : blockFour = .block 0 0 blockFive :: allocPhase := by rfl

private theorem shape_five : blockFive = .block 0 0 blockSix :: smallPhase := by rfl

private theorem shape_six :
    blockSix = .block 0 0 blockSeven :: overflowTailA := by rfl

private theorem shape_seven :
    blockSeven = itemsPhase (.block 0 0 blockCapacity :: rehashTail) := by rfl

private theorem shape_capacity :
    blockCapacity = capacityPhase (.block 0 0 blockClz :: overflowTailC) := by
  rfl

private theorem shape_clz : blockClz = clzPhase := by rfl

private theorem shape_commit_head :
    commitTail = commitHead (.block 0 0 blockFill :: commitMid) := by rfl

private theorem shape_fill : blockFill = fillPhase := by rfl

private theorem shape_commit_mid :
    commitMid = fullCapPhase (.block 0 0 blockResize :: commitEnd) := by rfl

private theorem shape_resize :
    blockResize = .localGet 6 :: .eqz :: .br_if 0 :: resizeTail := by rfl

private theorem shape_commit_end : commitEnd = storePhase freeTail := by rfl

/-! ## The allocator at alignment 8

Absolute `func 17` calls the allocator at alignment 8, WAT 3682 to 3686,
and `AllocatorContracts.Func55Spec` covers alignment 1 and alignment 4
only.  `AllocatorContracts.Func55SpecPow2` is the same contract with the
disjunct deleted, and `Func55Proof.func55_correct_pow2` proves it.  This
file takes it as a hypothesis, because it does not import
`Func55Proof.lean`. -/

/-- WAT 3665 to 3686: the slots and the control bytes in one block. -/
private def resizeLayout (buckets : Nat) : AllocLayout :=
  { size := 9 * buckets + 8, alignment := 8 }

private theorem resizeLayout_size (buckets : Nat) :
    (resizeLayout buckets).size = 9 * buckets + 8 := rfl

private theorem resizeLayout_valid {buckets : Nat} (hhigh : buckets ≤ 2 ^ 27) :
    (resizeLayout buckets).Valid := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  simp only [AllocLayout.Valid, resizeLayout]
  exact ⟨by omega, by omega, ⟨3, by norm_num⟩, by omega, by omega,
    by omega, by omega⟩

/-- A block frame of the compiled body.  Every block of `func 17` takes no
parameter and returns no value, and the stack is empty at each one. -/
@[reducible] private def blockFrame (body cont : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := body,
    continuation := cont, belowStack := [] }

private theorem func14_index :
    Project.RustHashMap.«module».funcs[14]? =
      some Project.RustHashMap.func14Def := by rfl

/-- The shift amount of `i32.shr_u` is already read modulo 32. -/
private theorem shrU_mod (x y : UInt32) : x >>> (y % 32) = x >>> y := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, UInt32.toNat_shiftRight, UInt32.toNat_mod]
  simp

/-- No positive word is at or below zero. -/
private theorem not_le_zero {x : UInt32} (h : 1 ≤ x.toNat) :
    ¬ (x ≤ (0 : UInt32)) := by
  intro hle
  have h' := UInt32.le_iff_toNat_le.mp hle
  have h0 : (0 : UInt32).toNat = 0 := rfl
  omega

/-- A sum that does not wrap. -/
private theorem toNat_add_nowrap {x y : UInt32}
    (h : x.toNat + y.toNat < 4294967296) :
    (x + y).toNat = x.toNat + y.toNat := by
  rw [UInt32.toNat_add]
  show (x.toNat + y.toNat) % 4294967296 = x.toNat + y.toNat
  omega

/-- No word is below zero. -/
private theorem not_lt_zero (x : UInt32) : ¬ (x < (0 : UInt32)) := by
  intro h
  have h' : x.toNat < (0 : UInt32).toNat := UInt32.lt_iff_toNat_lt.mp h
  have h0 : (0 : UInt32).toNat = 0 := rfl
  omega


/-- Move a word cell to an equal address that is written differently. -/
private theorem pointsTo_u32_at [WasmHeapGS Universal.State]
    {a b w : UInt32} (h : b = a) :
    pointsTo_u32 0 a w ⊢ pointsTo_u32 0 b w := by
  subst h
  iintro H
  iexact H

/-- The static empty table is four header words.  The control slice that
`Table.SingletonBody` also owns is dropped: the body of `func 17` never
reads it, and the coordinated window removes it from the predicate. -/
theorem TableAt_empty_open [WasmHeapGS Universal.State] (base : UInt32) :
    HashMap.Table.TableAt 0 base
        (HashMap.Table.empty (K := UInt32) (V := UInt32)) ⊢
      iprop(∃ ctrl : UInt32,
        pointsTo_u32 0 base ctrl ∗ pointsTo_u32 0 (base + 4) 0 ∗
          pointsTo_u32 0 (base + 8) 0 ∗ pointsTo_u32 0 (base + 12) 0) := by
  iintro Htable
  isimp only [HashMap.Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Hbody⟩
  icases Hbody with (Hsingleton | ⟨%hbuckets, Hbody⟩)
  · isimp only [HashMap.Table.SingletonBody, HashMap.Table.tableHeader]
      at Hsingleton
    icases Hsingleton with ⟨%hsing, ⟨H0, H4, H8, H12⟩, Hctrl⟩
    iexists ctrl
    iframe H0 H4 H8 H12
  · exact absurd hbuckets (by decide)


/-- The locals at the allocation, WAT 3665.  The two capacity branches
reach this point with the same machine state: the bucket count is in local
2, and every other live slot holds the value that phase A left there. -/
@[reducible] private def allocLocals (out table buckets hasher frame : UInt32) :
    Locals :=
  { params := [.i32 out, .i32 table, .i32 buckets, .i32 hasher, .i32 1],
    locals :=
      [.i32 frame, .i32 0, .i32 0, .i32 1, .i32 1, .i32 0, .i32 0, .i32 0,
        .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0],
    values := [] }

/-- The locals at the two calls of WAT 3681 to 3686.  Phase B has filled
local 9 with the byte count, local 11 with the bucket area and local 12
with the control area. -/
@[reducible] private def callLocals
    (out table buckets hasher frame total slots ctrlSize : UInt32) : Locals :=
  { params := [.i32 out, .i32 table, .i32 buckets, .i32 hasher, .i32 1],
    locals :=
      [.i32 frame, .i32 0, .i32 0, .i32 1, .i32 total, .i32 0, .i32 slots,
        .i32 ctrlSize, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0, .i64 0,
        .i64 0, .i64 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0],
    values := [] }

/-- The call frame that `Wasm.SmallStep.twp_call` pushes for the caller. -/
@[reducible] private def callerFrame (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) : CallFrame :=
  { locals :=
      { params := callerLocals.params, locals := callerLocals.locals,
        values := stack },
    continuation := code, resultArity := arity, callerRemainder := remainder,
    control := controls, returningInstance := ⟨0⟩ }


section BlockRule

variable [WasmSmallStepGS hlc Universal.State]

/-- Enter a block and keep the name of its body.  `Wasm.SmallStep.twp_block`
puts the body of the block into the new control frame, so a rewrite that
opens the body also rewrites the frame.  This rule opens the code alone. -/
private theorem twp_blockOf {params localValues : List Value}
    {body body' cont : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hbody : body = body') :
    WP (Expr.running
        ⟨⟨params, localValues, []⟩, body', arity, remainder,
          blockFrame body cont :: controls, calls⟩ :
        Expr Universal.State) @ s; E [{ Φ }] ⊢
      WP (Expr.running
        ⟨⟨params, localValues, []⟩, .block 0 0 body :: cont, arity, remainder,
          controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  subst hbody
  exact Wasm.SmallStep.twp_block

end BlockRule


section Machine

variable [WasmSmallStepGS hlc Universal.State]

set_option maxHeartbeats 2000000 in
/-- WAT 3665 to 4129: the allocation, the control fill, the header writes
and the epilogue.  Both capacity branches end here with the same locals, so
the tail is written once. -/
private theorem twp_commit
    (halloc : Func55SpecPow2 (hlc := hlc))
    (sp out table hasher additional bucketsWord ctrlOld : UInt32)
    (k0 k1 : UInt64) (outBefore below : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (callerLocals : Locals) (stack : List Value)
    (code : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (houtLength : outBefore.length = 8)
    (_hspLow : resizeDepth ≤ sp.toNat)
    (houtNowrap : out.toNat + 8 < UInt32.size)
    (htableNowrap : table.toNat + 16 < UInt32.size)
    (haLow : 1 ≤ additional.toNat)
    (haHigh : additional.toNat ≤ maxTableCapacity)
    (hbuckets : bucketsWord.toNat
      = HashMap.Table.capacityToBuckets additional.toNat) :
    iprop(RuntimeContext ∗
      StackPointer (sp - 32) ∗
      StackBelow sp resizeDepth below ∗
      Slices.ByteSlice 0 out outBefore ∗
      pointsTo_u32 0 table ctrlOld ∗
      pointsTo_u32 0 (table + 4) 0 ∗
      pointsTo_u32 0 (table + 8) 0 ∗
      pointsTo_u32 0 (table + 12) 0 ∗
      pointsTo_u64 0 hasher k0 ∗
      pointsTo_u64 0 (hasher + 8) k1 ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ word1 : UInt32, ∀ below' : List UInt8,
          ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
          ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer sp -∗
          StackBelow sp resizeDepth below' -∗
          Slices.ByteSlice 0 out
            (WordCodec.u32le.encode okTag ++
              WordCodec.u32le.encode word1) -∗
          HashMap.Table.TableAt 0 table
            (HashMap.Table.withCapacity additional.toNat) -∗
          pointsTo_u64 0 hasher k0 -∗
          pointsTo_u64 0 (hasher + 8) k1 -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ResumeWP [] callerLocals stack code arity remainder controls
            calls s E Φ) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (Expr.running
          ⟨allocLocals out table bucketsWord hasher (sp - 32), allocPhase,
            0, [],
            [blockFrame blockFour overflowTailB,
              blockFrame blockThree commitTail, blockFrame blockTwo [],
              blockFrame blockOne epiloguePhase],
            callerFrame callerLocals stack code arity remainder controls ::
              calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, H0, H4, H8, H12, Hk0, Hk1, Hbump,
    Hstreams, Hcont⟩
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  have hsz : UInt32.size = 4294967296 := rfl
  have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
  have h29 : (2 : Nat) ^ 29 = 536870912 := by norm_num
  have hBfour : 4 ≤ bucketsWord.toNat := by
    rw [hbuckets]; exact buckets_ge_four haLow haHigh
  have hBle : bucketsWord.toNat ≤ 2 ^ 27 := by
    rw [hbuckets]; exact buckets_le haHigh
  have hctrlNat : ((8 : UInt32) + bucketsWord).toNat = bucketsWord.toNat + 8 := by
    rw [UInt32.add_comm]
    exact toNat_add_lit (x := bucketsWord) (k := 8) (by omega)
  have hshlNat : (bucketsWord <<< (3 : UInt32)).toNat = bucketsWord.toNat * 8 :=
    toNat_shl3 (by omega)
  have htotalNat :
      (bucketsWord <<< (3 : UInt32) + ((8 : UInt32) + bucketsWord)).toNat
        = bucketsWord.toNat * 8 + (bucketsWord.toNat + 8) := by
    rw [toNat_add_nowrap (by rw [hshlNat, hctrlNat]; omega), hshlNat, hctrlNat]
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
    (callerLocals := callLocals out table bucketsWord hasher (sp - 32)
      (bucketsWord <<< 3 + ((8 : UInt32) + bucketsWord)) (bucketsWord <<< 3)
      ((8 : UInt32) + bucketsWord))
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
    have Halloc := halloc
    unfold Func55SpecPow2 CallContract callExpr at Halloc
    simp only [List.cons_append, List.nil_append] at Halloc
    iapply Halloc
      (size := bucketsWord <<< 3 + ((8 : UInt32) + bucketsWord))
      (alignment := 8) (layout := resizeLayout bucketsWord.toNat)
      (heapId := heapId) (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals := callLocals out table bucketsWord hasher (sp - 32)
        (bucketsWord <<< 3 + ((8 : UInt32) + bucketsWord)) (bucketsWord <<< 3)
        ((8 : UInt32) + bucketsWord))
      (stack := [])
    isplitl [Hmodule Henv]
    · unfold RuntimeContext
      iframe Hmodule Henv
    isplitl_exacts [Hbump Hstreams]
    isplitl_pureexact ⟨⟨by rw [htotalNat, resizeLayout_size]; omega, rfl⟩,
      resizeLayout_valid (by omega)⟩
    unfold AllocContinuation
    cases hdecision : classifyBump frontier (resizeLayout bucketsWord.toNat) with
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
          ihave Hbytes : Slices.ByteSlice 0 allocBase allocBytes $$ [Hallocbytes]
          · isimp only [Slices.ByteSlice]
            isplitl_pureexact (by rw [hbytesLength, resizeLayout_size, hsz]; omega)
            iexact Hallocbytes
          wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          iapply twp_brIf hbaseNonzero (by rfl)
          simp only [List.take_zero, List.nil_append]
          rw [shape_commit_head]
          -- WAT 3716 to 3719: `new_ctrl = base + 8 * buckets`
          wasm_twp_pures [twp_localGet twp_localGet twp_add]
          wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          iapply twp_blockOf shape_fill
          -- the allocation splits into the bucket area and the control area
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
          wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          rw [hmaskEq]
          wasm_twp_pures [twp_localGet twp_const twp_shrU]
          rw [show ((3 : UInt32) % 32) = 3 from by decide]
          wasm_twp_pures [twp_const twp_mul twp_localGet twp_const]
          iapply twp_ltU
            (result := if bucketsWord < (9 : UInt32) then (1 : UInt32) else 0) rfl
          iapply twp_select
            (selected := .i32 (UInt32.ofNat
              (HashMap.Table.bucketMaskToCapacity (bucketsWord.toNat - 1)))) (by
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
          wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          -- WAT 3743 to 3745: the old control pointer of the dead free
          ihave H0 := pointsTo_u32_at (UInt32.add_zero table) $$ H0
          wasm_twp_pures [twp_localGet]
          wasm_twp_rebind twp_load32 (address := table) (offset := 0) ctrlOld
            ht0.1 ht0.2.1 ht0.2.2.1 ht0.2.2.2 with H0
          wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          iapply twp_blockOf shape_resize
          -- WAT 3746 to 3749: the old table is empty, so the walk is dead
          wasm_twp_pures [twp_localGet]
          iapply twp_eqz (result := 1) (by rw [if_pos rfl])
          iapply twp_brIf (by decide) (by rfl)
          simp only [List.take_zero, List.nil_append]
          rw [shape_commit_end]
          have ht4b := offset_facts table 4 4 rfl (by omega)
          have ht8b := offset_facts table 8 8 rfl (by omega)
          -- WAT 4085 to 4092: the three header writes
          wasm_twp_pures [twp_localGet twp_localGet]
          wasm_twp_rebind twp_store32 (address := table) (offset := 4) 0
            ht4b.1 ht4b.2.1 ht4b.2.2.1 ht4b.2.2.2 with H4
          wasm_twp_pures [twp_localGet twp_localGet]
          wasm_twp_rebind twp_store32 (address := table) (offset := 0) ctrlOld
            ht0.1 ht0.2.1 ht0.2.2.1 ht0.2.2.2 with H0
          wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_sub]
          rw [UInt32.sub_zero]
          wasm_twp_rebind twp_store32 (address := table) (offset := 8) 0
            ht8b.1 ht8b.2.1 ht8b.2.2.1 ht8b.2.2.2 with H8
          -- WAT 4093 to 4097: the `Ok` tag and the guard of the dead free
          wasm_twp_pures [twp_const]
          wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
            Nat.reduceSub, List.set]
          rw [show (2147483649 : UInt32) = okTag from rfl]
          wasm_twp_pures [twp_localGet]
          iapply twp_eqz (result := 1) (by rw [if_pos rfl])
          iapply twp_brIf (by decide) (by rfl)
          simp only [List.take_zero, List.nil_append]
          iapply twp_exitControl (by rfl)
          simp only [List.take_zero, List.nil_append]
          -- WAT 4119 to 4126: the result slot
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
            Slices.ByteSlice_storeWordFocus 0 (out + 4) (outBefore.drop 4) bucketsWord
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
            (WordCodec.u32le.serialize [bucketsWord]) 4 (by decide)
            $$ [Hlow Hhigh]
          · isplitl_exact Hlow
            · irw_exact [show UInt32.ofNat 4 = (4 : UInt32) from rfl] with Hhigh
          isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
            List.append_nil] at Hout
          -- WAT 4127 to 4129: the stack pointer
          isimp only [StackPointer] at Hsp
          wasm_twp_pures [twp_localGet twp_const twp_add]
          rw [show (32 : UInt32) + (sp - 32) = sp by
            rw [UInt32.add_comm, UInt32.sub_add_cancel]]
          wasm_twp_rebind twp_globalSet with Hsp
          wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
          simp only [List.take_zero, List.nil_append]
          -- the freshly built table
          have hnewCtrlNat : (bucketsWord <<< 3 + allocBase).toNat
              = bucketsWord.toNat * 8 + allocBase.toNat := by
            rw [toNat_add_nowrap (by rw [hshlNat]; omega), hshlNat]
          isimp only [hdropLength, HashMap.Table.toUInt8_fillByte] at Hctrlbytes
          ihave H0 := pointsTo_u32_at (UInt32.add_zero table).symm $$ H0
          ihave Hbody := HashMap.Table.TableBody_newEmpty 0 table allocBase
            (bucketsWord <<< 3 + allocBase) bucketsWord.toNat
            (allocBytes.take (8 * bucketsWord.toNat)) htakeLength hctrlAddr
            (by rw [hnewCtrlNat]; omega) (by rw [hnewCtrlNat, hsz]; omega)
            $$ [H0 H4 H8 H12 Hslots Hctrlbytes]
          · isplitl [H0 H4 H8 H12]
            · isimp only [HashMap.Table.tableHeader]
              iframe H0 H4 H8 H12
            · isplitl_exact Hslots
              · iexact Hctrlbytes
          have hwc : (HashMap.Table.withCapacity additional.toNat
              : HashMap.Table UInt32 UInt32)
              = HashMap.Table.newEmpty bucketsWord.toNat := by
            unfold HashMap.Table.withCapacity
            rw [if_neg (by omega), ← hbuckets]
          ihave Htable : HashMap.Table.TableAt 0 table
              (HashMap.Table.withCapacity additional.toNat) $$ [Hbody]
          · rw [hwc]
            isimp only [HashMap.Table.TableAt]
            iexists (bucketsWord <<< 3 + allocBase)
            iright
            isplitl_pureexact (show 1 < bucketsWord.toNat by omega)
            iexact Hbody
          iclose_map_runtime Hruntime with Hmodule Henv
          ihave Hsp : StackPointer sp $$ [Hsp]
          · unfold StackPointer
            iexact Hsp
          ihave Hnormal := BI.and_elim_l $$ Hcont
          ihave Hnormal := Hnormal $$ %bucketsWord %below %finish
            %(finish.toNat)
            %(history.allocate allocBase (resizeLayout bucketsWord.toNat))
          iapply Hnormal $$ Hruntime Hsp Hbelow Hout Htable Hk0 Hk1 Hbump
            Hstreams
        · iintro Hbump Hstreams
          ihave Hoom := BI.and_elim_r $$ Hcont
          iapply Hoom $$ %input Hstreams


set_option maxHeartbeats 2000000 in
theorem func14_correct_of (halloc : Func55SpecPow2 (hlc := hlc)) :
    Func14Spec (hlc := hlc) := by
  unfold Func14Spec CallContract callExpr
  intro sp out table additional hasher k0 k1 t outBefore below heapId
    storedCursor frontier history input output raised callerLocals stack
    code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Htable, Hk0, Hk1, Hbump, Hstreams,
    %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, htableNowrap, hhasherNowrap,
    htempty, haLow, haHigh⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 17
      Project.RustHashMap.func14Def (by decide) func14_index with Hmodule
  simp [Project.RustHashMap.func14Def, Function.toLocals, Function.numParams,
    ValueType.zero]
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
  -- the four header words of the static empty table
  subst htempty
  ihave ⟨%ctrlOld, H0, H4, H8, H12⟩ := TableAt_empty_open table $$ Htable
  have ht4 := offset_facts table 4 4 rfl (by omega)
  have ht8 := offset_facts table 8 8 rfl (by omega)
  have ht12 := offset_facts table 12 12 rfl (by omega)
  -- WAT 3027 to 3041: `new_items = items + additional`, which never wraps
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind twp_load32 (address := table) (offset := 12) 0
    ht12.1 ht12.2.1 ht12.2.2.1 ht12.2.2.2 with H12
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_add]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  iapply twp_ltU (result := 0) (by rw [if_neg (not_lt_zero _)])
  iapply twp_brIfZero
  simp only [UInt32.add_zero]
  iapply twp_blockOf shape_capacity
  -- WAT 3043 to 3060: `full_cap = if mask < 8 then mask else buckets / 8 * 7`
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := table) (offset := 4) 0
    ht4.1 ht4.2.1 ht4.2.2.1 ht4.2.2.2 with H4
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  simp only [UInt32.add_zero]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_shrU]
  rw [show ((1 : UInt32) >>> ((3 : UInt32) % 32)) = 0 from by decide]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_mul twp_localGet twp_const]
  iapply twp_ltU (result := 1) (by rw [if_pos (by decide : (0 : UInt32) < 8)])
  iapply twp_select (selected := .i32 0) (by rw [if_pos (by decide)])
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- WAT 3063 to 3064: the rehash-in-place arm is dead
  wasm_twp_pures [twp_const twp_shrU]
  rw [show ((0 : UInt32) >>> ((1 : UInt32) % 32)) = 0 from by decide]
  iapply twp_leU (result := 0) (by rw [if_neg (not_le_zero haLow)])
  iapply twp_brIfZero
  -- WAT 3065 to 3077: `cap = max (new_items, full_cap + 1)`
  wasm_twp_pures [twp_localGet twp_const twp_add]
  simp only [UInt32.add_zero]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  iapply twp_gtU (result := 0) (by
    rw [if_neg (by
      intro hgt
      have h' := UInt32.lt_iff_toNat_lt.mp hgt
      have h1 : (1 : UInt32).toNat = 1 := rfl
      omega)])
  iapply twp_select (selected := .i32 additional) (by rw [if_neg (by decide)])
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  have hsz : UInt32.size = 4294967296 := rfl
  have h4nat : (4 : UInt32).toNat = 4 := rfl
  have h15nat : (15 : UInt32).toNat = 15 := rfl
  by_cases hsmall : additional < 15
  · -- WAT 3653 to 3663: fewer than fifteen entries
    have ha15 : additional.toNat < 15 := by
      have h := UInt32.lt_iff_toNat_lt.mp hsmall
      omega
    iapply twp_ltU (result := 1) (by rw [if_pos hsmall])
    iapply twp_brIf (by decide) (by rfl)
    wasm_twp_pures [twp_const twp_localGet twp_const twp_and twp_const
      twp_add twp_localGet twp_const]
    by_cases htiny : additional < 4
    · -- three entries or fewer: four buckets
      have ha4 : additional.toNat < 4 := by
        have h := UInt32.lt_iff_toNat_lt.mp htiny
        omega
      have hbuck : (4 : UInt32).toNat
          = HashMap.Table.capacityToBuckets additional.toNat := by
        rw [h4nat, buckets_tiny haLow ha4]
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
      iapply twp_commit halloc sp out table hasher additional 4 ctrlOld k0 k1
        outBefore below heapId storedCursor frontier history input output
        raised callerLocals stack code arity remainder controls calls s E Φ
        houtLength hspLow houtNowrap htableNowrap haLow haHigh hbuck
      iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 Hk0 Hk1 Hbump Hstreams
      iexact Hcont
    · -- four to fourteen entries: eight or sixteen buckets
      have ha4 : 4 ≤ additional.toNat := by
        by_contra hcon
        exact htiny (UInt32.lt_iff_toNat_lt.mpr (by omega))
      have h8nat : (8 : UInt32).toNat = 8 := rfl
      have hand : (additional &&& 8).toNat ≤ 8 := by
        rw [UInt32.toNat_and, h8nat]
        exact Nat.and_le_right
      have hbuck : ((8 : UInt32) + (additional &&& 8)).toNat
          = HashMap.Table.capacityToBuckets additional.toNat := by
        have hadd : ((8 : UInt32) + (additional &&& 8)).toNat
            = (additional &&& 8).toNat + 8 := by
          rw [UInt32.add_comm]
          exact toNat_add_lit (x := additional &&& 8) (k := 8) (by omega)
        rw [hadd, UInt32.toNat_and, h8nat]
        exact buckets_small ha4 ha15
      iapply twp_ltU (result := 0) (by rw [if_neg htiny])
      iapply twp_select (selected := .i32 ((8 : UInt32) + (additional &&& 8)))
        (by rw [if_neg (by decide)])
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      iapply twp_exitControl (by rfl)
      simp only [List.take_zero, List.nil_append]
      iclose_map_runtime Hruntime with Hmodule Henv
      ihave Hsp : StackPointer (sp - 32) $$ [Hsp]
      · unfold StackPointer
        iexact Hsp
      iapply twp_commit halloc sp out table hasher additional
        ((8 : UInt32) + (additional &&& 8)) ctrlOld k0 k1
        outBefore below heapId storedCursor frontier history input output
        raised callerLocals stack code arity remainder controls calls s E Φ
        houtLength hspLow houtNowrap htableNowrap haLow haHigh hbuck
      iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 Hk0 Hk1 Hbump Hstreams
      iexact Hcont
  · -- WAT 3079 to 3100: fifteen entries or more, the count-leading-zeros arm
    have hmaxEq : maxTableCapacity = 117440512 := rfl
    have haNum : additional.toNat ≤ 117440512 := by
      rw [hmaxEq] at haHigh; exact haHigh
    have ha15 : 15 ≤ additional.toNat := by
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
    have hshl : (additional <<< (3 : UInt32)).toNat = additional.toNat * 8 :=
      toNat_shl3 (by
        have h29 : (2 : Nat) ^ 29 = 536870912 := by norm_num
        omega)
    have hq : ((additional <<< (3 : UInt32)) / 7).toNat
        = additional.toNat * 8 / 7 := by
      rw [UInt32.toNat_div, hshl, show (7 : UInt32).toNat = 7 from rfl]
    have hofn : (4294967295 : UInt32) + ((additional <<< (3 : UInt32)) / 7)
        = UInt32.ofNat (additional.toNat * 8 / 7 - 1) := by
      apply UInt32.toNat_inj.mp
      rw [UInt32.add_comm, toNat_pred (by rw [hq]; omega), hq]
      exact (UInt32.toNat_ofNat_of_lt' (by omega)).symm
    rw [hofn]
    set tWord : UInt32 := (0xFFFFFFFF : UInt32) >>>
      UInt32.ofNat (clz32 32 (UInt32.ofNat (additional.toNat * 8 / 7 - 1)))
      with htdef
    have hbig : tWord.toNat + 1
        = HashMap.Table.capacityToBuckets additional.toNat := by
      rw [htdef]; exact buckets_big ha15 haHigh
    have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
    have htle : tWord.toNat + 1 ≤ 2 ^ 27 := by
      rw [hbig]; exact buckets_le haHigh
    have hadd1 : (tWord + (1 : UInt32)).toNat = tWord.toNat + 1 :=
      toNat_add_lit (x := tWord) (k := 1) (by omega)
    have hbuck : ((1 : UInt32) + tWord).toNat
        = HashMap.Table.capacityToBuckets additional.toNat := by
      rw [UInt32.add_comm, hadd1]
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
    iapply twp_commit halloc sp out table hasher additional
      ((1 : UInt32) + tWord) ctrlOld k0 k1
      outBefore below heapId storedCursor frontier history input output
      raised callerLocals stack code arity remainder controls calls s E Φ
      houtLength hspLow houtNowrap htableNowrap haLow haHigh hbuck
    iframe Hruntime Hsp Hbelow Hout H0 H4 H8 H12 Hk0 Hk1 Hbump Hstreams
    iexact Hcont

end Machine

end Project.RustHashMap.Func14Proof
