import Project.RustHashMap.Program

/-!
# `quicksort`: the named fragments of the body

Absolute `func 24` is local `func21`.  WAT lines 5670 to 8663 of
`programs/rust/build/rust_hash_map/program.wat` hold it, which is 2994
lines.  Its contract is `Project.RustHashMap.SortContracts.Func21Spec`.

Five proof files share the body: the partition, the two sorting
networks, the small sort and the assembly.  Each file proves one region.
This file gives the one set of fragment names that all five use.  It
holds definitions and shape lemmas only.  It proves no Hoare triple.

## How a fragment is built

The body of a block is not a suffix of the list that holds the block, so
`blockBody` takes it from the head instruction.  Every fragment below
comes from `Project.RustHashMap.func21` by `blockBody`, `List.drop` and
`List.take`.  No fragment uses `++`, because a `simp only` that unfolds
`++` also unfolds the definition that `twp_block` put in a control
frame.  A fragment that starts a block or a loop is therefore a cons
cell, and the tactic that steps through pure instructions can reduce it.

Each shape lemma is `rfl`.  The shape lemmas carry the content: they
pin each fragment to the generated code.  A `_split` lemma names the
parts of a straight-line run and does use `++`, because a proof rewrites
with it once and never unfolds it again.

## The signature

The function takes five arguments.  Local 0 is the buffer, local 1 the
length, local 2 the ancestor pivot address, local 3 the recursion limit
and local 4 the comparison closure.  The body declares 34 more locals,
so the last index is 38.  Local 5 holds the frame pointer.  The frame is
256 bytes.

## The regions

The body has two halves.  The first half is the quicksort loop, which
runs while the length is 33 or more.  The second half is the small sort,
which sorts one or two regions and then merges them.

The quicksort loop, WAT 5685 to 6191, does four steps in each turn:

1. It leaves to `call 25` when the recursion limit reaches zero.
2. It picks a pivot, with `call 23` for a long input and with an inline
   median for a short one.
3. It partitions.  The equal-key partition of WAT 5758 to 5976 runs when
   the ancestor key equals the pivot key.  `AncestorBelow` kills that
   arm, so the arm is dead.  The strict partition of WAT 5977 to 6151
   runs in every live case.
4. It calls itself on the left part and then loops on the right part.

The small sort, WAT 6193 to 8652, does three steps:

1. It splits the input into one or two regions.
2. It sorts each region.  A region of 9 to 12 items goes through the
   sorting network of WAT 6233 to 7008, and a region of 13 to 18 items
   goes through the network of WAT 7011 to 8391.  Both networks are
   branch free.  A region of 19 items or more goes through the insertion
   sort of WAT 8397 to 8489.
3. It merges the two regions into the frame and copies the result back.

## The two sorting networks

Each network is one straight-line run.  A comparator is three `select`
instructions.  The first network holds 75 `select` instructions, which
is 25 comparators, and the second holds 135, which is 45 comparators.
`qsSort9Chunk` and `qsSort13Chunk` cut each network into pieces of five
comparators, so that a chunk lemma stays inside the heartbeat limit.  A
chunk boundary sits at the instruction after the 15th, 30th, and so on
`select`.  The last chunk takes the three instructions that follow the
last comparator as well.
-/

namespace Project.RustHashMap.Func21Defs

open Wasm
open Wasm.SmallStep

set_option maxRecDepth 40000

/-- The body of the block or the loop that starts a program fragment. -/
def blockBody (p : Program) : Program :=
  match p with
  | .block _ _ body :: _ => body
  | .loop _ _ body :: _ => body
  | _ => []

/-- Count the `select` instructions of a fragment.  `Instruction` has no
`BEq` instance, so the test is a match. -/
def isSelect : Instruction → Bool
  | .select => true
  | _ => false

/-! ## The raw extraction

Each `raw` name takes one block body from the generated code.  The
public fragments below are stated in terms of these, so that every shape
lemma closes by `rfl`. -/

private def raw1 : Program :=
  blockBody (Project.RustHashMap.func21.drop 5)
private def raw2 : Program := blockBody raw1
private def raw3 : Program := blockBody raw2
private def raw4 : Program := blockBody raw3
private def rawLoop5 : Program := blockBody (raw4.drop 4)
private def rawHeap : Program := blockBody rawLoop5
private def rawMedian : Program := blockBody (rawLoop5.drop 16)
private def rawMedianCall : Program := blockBody rawMedian
private def rawPart : Program := blockBody (rawLoop5.drop 25)
private def rawEqual : Program := blockBody rawPart
private def rawEqualFwd : Program := blockBody (rawEqual.drop 34)
private def rawEqualFwdPre : Program := blockBody rawEqualFwd
private def rawEqualFwdLoop : Program := blockBody (rawEqualFwd.drop 3)
private def rawEqualBack : Program := blockBody (rawEqual.drop 38)
private def rawEqualBackLoop : Program := blockBody (rawEqualBack.drop 4)
private def rawAfterEqual : Program := rawPart.drop 1
private def rawStrictFwd : Program := blockBody (rawAfterEqual.drop 25)
private def rawStrictFwdPre : Program := blockBody rawStrictFwd
private def rawStrictFwdLoop : Program := blockBody (rawStrictFwd.drop 3)
private def rawStrictBack : Program := blockBody (rawAfterEqual.drop 29)
private def rawStrictBackLoop : Program :=
  blockBody (rawStrictBack.drop 4)
private def rawAfter4 : Program := raw3.drop 1
private def rawRegionLoop : Program := blockBody (rawAfter4.drop 27)
private def rawRegionBody : Program := blockBody rawRegionLoop
private def rawNetwork : Program := blockBody rawRegionBody
private def rawInsertion : Program := blockBody (rawRegionLoop.drop 5)
private def rawInsertOuter : Program := blockBody (rawInsertion.drop 17)
private def rawInsertCheck : Program := blockBody rawInsertOuter
private def rawShiftBlock : Program :=
  blockBody (rawInsertCheck.drop 14)
private def rawInsertShift : Program := blockBody rawShiftBlock
private def rawInsertInner : Program := blockBody (rawInsertShift.drop 9)
private def rawMerge : Program := blockBody (rawAfter4.drop 49)
private def rawMergeOdd : Program := blockBody (rawAfter4.drop 54)

/-! ## The frame setup and the four outer blocks -/

/-- The frame setup, WAT 5672 to 5676.  It takes 256 bytes below the
stack pointer and writes the new frame pointer to local 5. -/
@[reducible] def qsPrologue : Program :=
  Project.RustHashMap.func21.take 5

/-- The stack epilogue, WAT 8659 to 8662. -/
@[reducible] def qsEpilogue : Program :=
  Project.RustHashMap.func21.drop 6

/-- The code after the end of block `@1`, WAT 8659 to 8662.  It is the
epilogue, so every exit of the body joins it. -/
@[reducible] def qsAfter1 : Program := qsEpilogue

/-- The body of block `@1`, WAT 5678 to 8657. -/
@[reducible] def qsBlock1Body : Program := raw1

/-- The code after the end of block `@2`, WAT 8656 to 8657.  `call 107`
is the panic that a comparison which is not a strict total order raises,
so the arm is dead. -/
@[reducible] def qsAfter2 : Program := raw1.drop 1

/-- The body of block `@2`, WAT 5679 to 8654. -/
@[reducible] def qsBlock2Body : Program := raw2

/-- The code after the end of block `@3`, WAT 8654.  Every branch that
reaches it is dead. -/
@[reducible] def qsAfter3 : Program := raw2.drop 1

/-- The body of block `@3`, WAT 5680 to 8652. -/
@[reducible] def qsBlock3Body : Program := raw3

/-- The code after the end of block `@4`, WAT 6193 to 8652.  It is the
small sort, which runs when the length is 32 or less. -/
@[reducible] def qsAfter4 : Program := rawAfter4

/-- The body of block `@4`, WAT 5681 to 6191.  It tests the length and
then runs the quicksort loop. -/
@[reducible] def qsBlock4Body : Program := raw4

/-- The length test at the head of block `@4`, WAT 5681 to 5684.  A
length below 33 leaves the block. -/
@[reducible] def qsLenGuard : Program := raw4.take 4

/-! ## The quicksort loop -/

/-- The body of the loop `@5`, WAT 5686 to 6190. -/
@[reducible] def qsLoopBody : Program := rawLoop5

/-- The body of the block `@6` at WAT 5686, which is WAT 5687 to 5693.
The recursion limit reaches zero here, so the body calls the heap sort
`func 25` and leaves.  This is the live edge X-F24-HEAP. -/
@[reducible] def qsHeapArm : Program := rawHeap

/-- The code after the heap arm, WAT 5695 to 6190. -/
@[reducible] def qsAfterHeap : Program := rawLoop5.drop 1

/-- The two pivot candidates, WAT 5695 to 5709.  Local 6 holds the
length divided by eight, local 7 the address of candidate `56 * local 6`
and local 8 the address of candidate `32 * local 6`. -/
@[reducible] def qsPivotSetup : Program := (rawLoop5.drop 1).take 15

/-- The pivot choice, WAT 5695 to 5757.  `qsPivotSetup` and the block at
WAT 5710 make it up. -/
@[reducible] def qsMedian : Program := (rawLoop5.drop 1).take 24

/-- The body of the block `@6` at WAT 5710, which is WAT 5711 to 5748.
It chooses between the call and the inline median. -/
@[reducible] def qsMedianBlock : Program := rawMedian

/-- The body of the block `@7` at WAT 5711, which is WAT 5712 to 5722.
A length of 64 or more goes to `call 23`, the median of medians. -/
@[reducible] def qsMedianCall : Program := rawMedianCall

/-- The inline median of three, WAT 5724 to 5748.  A length below 64
reaches it.  It writes the pivot address to local 6. -/
@[reducible] def qsMedianInline : Program := rawMedian.drop 1

/-- The code after the pivot choice, WAT 5750 to 6190. -/
@[reducible] def qsAfterMedian : Program := rawLoop5.drop 17

/-- The limit decrement and the pivot offset, WAT 5750 to 5757.  Local 3
loses one and local 6 becomes the pivot offset in bytes. -/
@[reducible] def qsLimitDec : Program := (rawLoop5.drop 17).take 8

/-- The body of the block `@6` at WAT 5758, which is WAT 5759 to 6185.
It holds both partitions and the recursion. -/
@[reducible] def qsPartitionBody : Program := rawPart

/-- The back edge test of the loop `@5`, WAT 6187 to 6190.  A length of
33 or more turns again. -/
@[reducible] def qsLoopGuard : Program := rawLoop5.drop 26

/-! ## The equal-key partition, WAT 5758 to 5976

`AncestorBelow` says that the ancestor key is below every key of the
input, so the guard at WAT 5763 always leaves this block.  The arm is
the dead edge X-F24-EQUAL. -/

/-- The body of the block `@7` at WAT 5759, which is WAT 5760 to 5975. -/
@[reducible] def qsEqualPartition : Program := rawEqual

/-- The two guards of the equal-key partition, WAT 5760 to 5771.  A zero
ancestor leaves, and an ancestor key below the pivot key leaves. -/
@[reducible] def qsEqualGuard : Program := rawEqual.take 12

/-- The swap that puts the pivot first, WAT 5772 to 5793. -/
@[reducible] def qsEqualSwap : Program := (rawEqual.drop 12).take 22

/-- The body of the block `@8` at WAT 5794, which is WAT 5795 to 5877.
It scans forward for a key that is not equal to the pivot key. -/
@[reducible] def qsEqualScanFwd : Program := rawEqualFwd

/-- The body of the block `@9` at WAT 5795, which is WAT 5796 to 5813.
It is the first turn of the forward scan. -/
@[reducible] def qsEqualFwdPre : Program := rawEqualFwdPre

/-- The two instructions between the first turn and the loop, WAT 5815
to 5816. -/
@[reducible] def qsEqualFwdMid : Program := (rawEqualFwd.drop 1).take 2

/-- The body of the loop `@9` at WAT 5817, which is WAT 5818 to 5872. -/
@[reducible] def qsEqualFwdLoop : Program := rawEqualFwdLoop

/-- The code after the forward scan loop, WAT 5874 to 5877. -/
@[reducible] def qsEqualFwdTail : Program := rawEqualFwd.drop 4

/-- The three instructions between the two scans, WAT 5879 to 5881. -/
@[reducible] def qsEqualMid : Program := (rawEqual.drop 35).take 3

/-- The body of the block `@8` at WAT 5882, which is WAT 5883 to 5922.
It scans back for a key that is not equal to the pivot key. -/
@[reducible] def qsEqualScanBack : Program := rawEqualBack

/-- The first turn of the back scan, WAT 5883 to 5886. -/
@[reducible] def qsEqualBackPre : Program := rawEqualBack.take 4

/-- The body of the loop `@9` at WAT 5887, which is WAT 5888 to 5917. -/
@[reducible] def qsEqualBackLoop : Program := rawEqualBackLoop

/-- The code after the back scan loop, WAT 5919 to 5922. -/
@[reducible] def qsEqualBackTail : Program := rawEqualBack.drop 5

/-- The write back and the rotation of the equal-key partition, WAT 5924
to 5975.  The `br_if 4` at WAT 5944 is dead, because the split never
reaches the length. -/
@[reducible] def qsEqualWriteBack : Program := rawEqual.drop 39

/-! ## The strict partition, WAT 5977 to 6151 -/

/-- The code after the equal-key partition, WAT 5977 to 6185.  It is the
strict partition and the recursion. -/
@[reducible] def qsAfterEqual : Program := rawAfterEqual

/-- The strict partition, WAT 5977 to 6151.  It writes the split index
to local 6. -/
@[reducible] def qsStrictPartition : Program := rawAfterEqual.take 50

/-- The setup of the strict partition, WAT 5977 to 6001. -/
@[reducible] def qsStrictSetup : Program := rawAfterEqual.take 25

/-- The body of the block `@7` at WAT 6002, which is WAT 6003 to 6085.
It scans forward for a key that is not below the pivot key. -/
@[reducible] def qsStrictScanFwd : Program := rawStrictFwd

/-- The body of the block `@8` at WAT 6003, which is WAT 6004 to 6021.
It is the first turn of the forward scan. -/
@[reducible] def qsStrictFwdPre : Program := rawStrictFwdPre

/-- The two instructions between the first turn and the loop, WAT 6023
to 6024. -/
@[reducible] def qsStrictFwdMid : Program := (rawStrictFwd.drop 1).take 2

/-- The body of the loop `@8` at WAT 6025, which is WAT 6026 to 6080. -/
@[reducible] def qsStrictFwdLoop : Program := rawStrictFwdLoop

/-- The code after the forward scan loop, WAT 6082 to 6085. -/
@[reducible] def qsStrictFwdTail : Program := rawStrictFwd.drop 4

/-- The three instructions between the two scans, WAT 6087 to 6089. -/
@[reducible] def qsStrictMid : Program := (rawAfterEqual.drop 26).take 3

/-- The body of the block `@7` at WAT 6090, which is WAT 6091 to 6130.
It scans back for a key that is below the pivot key. -/
@[reducible] def qsStrictScanBack : Program := rawStrictBack

/-- The first turn of the back scan, WAT 6091 to 6094. -/
@[reducible] def qsStrictBackPre : Program := rawStrictBack.take 4

/-- The body of the loop `@8` at WAT 6095, which is WAT 6096 to 6125. -/
@[reducible] def qsStrictBackLoop : Program := rawStrictBackLoop

/-- The code after the back scan loop, WAT 6127 to 6130. -/
@[reducible] def qsStrictBackTail : Program := rawStrictBack.drop 5

/-- The write back of the strict partition, WAT 6132 to 6151.  Local 6
becomes the split index. -/
@[reducible] def qsStrictWriteBack : Program :=
  (rawAfterEqual.drop 30).take 20

/-- The recursion and the tail update, WAT 6152 to 6185.  The `br_if 3`
at WAT 6152 is dead, because the split stays below the length.  WAT 6153
to 6172 swap the pivot into place, WAT 6173 calls `func 24` on the left
part, and WAT 6174 to 6185 move the buffer, the length and the ancestor
to the right part. -/
@[reducible] def qsRecurse : Program := rawAfterEqual.drop 50

/-! ## The small sort -/

/-- The split into regions, WAT 6193 to 6219.  A length below 2 leaves.
Local 16 holds the half length, local 17 the test `length < 18`, local 7
the length of the first region, local 18 the length of the second
region, local 13 the address of the second region and local 8 the
address of the region that runs now. -/
@[reducible] def qsSmallSetup : Program := rawAfter4.take 27

/-- The body of the loop `@4` at WAT 6220, which is WAT 6221 to 8501.
It sorts one region in each turn. -/
@[reducible] def qsRegionLoop : Program := rawRegionLoop

/-- The body of the block `@5` at WAT 6221, which is WAT 6222 to 8391.
It holds the two sorting networks. -/
@[reducible] def qsRegionBody : Program := rawRegionBody

/-- The body of the block `@6` at WAT 6222, which is WAT 6223 to 7009.
It tests the region length and holds the first network. -/
@[reducible] def qsNetworkSelect : Program := rawNetwork

/-- The region length test, WAT 6223 to 6232.  A length above 12 leaves
the block and reaches the second network.  A length of 8 or less leaves
block `@5` with local 6 set to one, so the insertion sort runs. -/
@[reducible] def qsSmallGuard : Program := rawNetwork.take 10

/-- The first sorting network, WAT 6233 to 7008.  It sorts 9 to 12 items
and then writes 9 to local 6.  The run is branch free and holds 75
`select` instructions, which is 25 comparators. -/
@[reducible] def qsSort9 : Program := (rawNetwork.drop 10).take 776

/-- The second sorting network, WAT 7011 to 8391.  It sorts 13 to 18
items and then writes 13 to local 6.  The run is branch free and holds
135 `select` instructions, which is 45 comparators. -/
@[reducible] def qsSort13 : Program := rawRegionBody.drop 1

/-- The code after the sorting networks, WAT 8393 to 8501. -/
@[reducible] def qsAfterRegionBody : Program := rawRegionLoop.drop 1

/-- The order test, WAT 8393 to 8396.  The `br_if 1` is dead, because
the network length never passes the region length. -/
@[reducible] def qsRegionOrder : Program := (rawRegionLoop.drop 1).take 4

/-- The body of the block `@5` at WAT 8397, which is WAT 8398 to 8488.
It is the insertion sort that finishes a region. -/
@[reducible] def qsInsertion : Program := rawInsertion

/-- The setup of the insertion sort, WAT 8398 to 8414.  An already
sorted region leaves at WAT 8401. -/
@[reducible] def qsInsertSetup : Program := rawInsertion.take 17

/-- The body of the outer loop `@6` at WAT 8415, which is WAT 8416 to
8487.  It places one item in each turn. -/
@[reducible] def qsInsertOuter : Program := rawInsertOuter

/-- The body of the block `@7` at WAT 8416, which is WAT 8417 to 8475.
It tests whether the new item is already in order. -/
@[reducible] def qsInsertCheck : Program := rawInsertCheck

/-- The order test of the outer loop, WAT 8417 to 8430. -/
@[reducible] def qsInsertCheckHead : Program := rawInsertCheck.take 14

/-- The body of the block `@8` at WAT 8431, which is WAT 8432 to 8466.
It holds the shift loop. -/
@[reducible] def qsInsertShiftBlock : Program := rawShiftBlock

/-- The body of the shift loop `@9` at WAT 8432, which is WAT 8433 to
8461.  It moves one item up in each turn. -/
@[reducible] def qsInsertShift : Program := rawInsertShift

/-- The body of the block `@10` at WAT 8442, which is WAT 8443 to 8449.
It stops the shift when the place is found. -/
@[reducible] def qsInsertInner : Program := rawInsertInner

/-- The code after the block `@10`, WAT 8451 to 8461. -/
@[reducible] def qsInsertShiftBack : Program := rawInsertShift.drop 10

/-- The code after the shift loop, WAT 8463 to 8466. -/
@[reducible] def qsInsertShiftTail : Program := rawShiftBlock.drop 1

/-- The code after the block `@8`, WAT 8468 to 8475. -/
@[reducible] def qsInsertCheckTail : Program := rawInsertCheck.drop 15

/-- The back edge test of the outer loop, WAT 8477 to 8487. -/
@[reducible] def qsInsertTail : Program := rawInsertOuter.drop 1

/-- The step to the second region, WAT 8490 to 8501.  A length below 18
has one region only, so local 17 leaves the small sort at WAT 8491. -/
@[reducible] def qsRegionNext : Program := rawRegionLoop.drop 6

/-! ## The merge -/

/-- The code after the region loop, WAT 8503 to 8652. -/
@[reducible] def qsAfterRegion : Program := rawAfter4.drop 28

/-- The setup of the merge, WAT 8503 to 8523.  Local 7 holds the last
address of the first region, local 8 the last address of the second
region, local 9 the frame base, local 10 the last frame address and
local 6 the buffer base. -/
@[reducible] def qsMergeSetup : Program := (rawAfter4.drop 28).take 21

/-- The body of the merge loop `@4` at WAT 8524, which is WAT 8525 to
8595.  It takes one item from each end in each turn and counts local 16
down. -/
@[reducible] def qsMerge : Program := rawMerge

/-- The code after the merge loop, WAT 8597 to 8652. -/
@[reducible] def qsAfterMerge : Program := rawAfter4.drop 50

/-- The middle item, WAT 8597 to 8631.  An odd length leaves one item,
which the block at WAT 8601 moves with a `select`. -/
@[reducible] def qsMergeMiddle : Program := (rawAfter4.drop 50).take 5

/-- The pointer step before the middle item, WAT 8597 to 8600. -/
@[reducible] def qsMergeAdvance : Program := (rawAfter4.drop 50).take 4

/-- The body of the block `@4` at WAT 8601, which is WAT 8602 to 8630.
An even length leaves it at once. -/
@[reducible] def qsMergeOdd : Program := rawMergeOdd

/-- The pointer checks after the merge, WAT 8632 to 8647.  Both `br_if 1`
branches are dead, because the merge meets in the middle.  A length of
zero leaves at WAT 8647, which the length test at WAT 6196 already
stops. -/
@[reducible] def qsPointerCheck : Program := (rawAfter4.drop 55).take 16

/-- The copy back, WAT 8648 to 8652.  It moves `8 * length` bytes from
the frame to the buffer and then leaves the body. -/
@[reducible] def qsCopy : Program := rawAfter4.drop 71

/-! ## The shape of the function

Every lemma below closes by `rfl`, so the generated code and the
fragments agree by definition. -/

theorem func21_shape :
    Project.RustHashMap.func21 =
      .globalGet 0 :: .const 256 :: .sub :: .localTee 5 ::
        .globalSet 0 :: .block 0 0 qsBlock1Body :: qsAfter1 := by
  rfl

theorem qsEpilogue_shape :
    qsEpilogue = [.localGet 5, .const 256, .add, .globalSet 0] := by
  rfl

theorem qsBlock1Body_shape :
    qsBlock1Body = .block 0 0 qsBlock2Body :: qsAfter2 := by
  rfl

theorem qsAfter2_shape : qsAfter2 = [.call 107, .unreachable] := by
  rfl

theorem qsBlock2Body_shape :
    qsBlock2Body = .block 0 0 qsBlock3Body :: qsAfter3 := by
  rfl

theorem qsAfter3_shape : qsAfter3 = [.unreachable] := by
  rfl

theorem qsBlock3Body_shape :
    qsBlock3Body = .block 0 0 qsBlock4Body :: qsAfter4 := by
  rfl

theorem qsBlock4Body_shape :
    qsBlock4Body =
      [.localGet 1, .const 33, .ltU, .br_if 0, .loop 0 0 qsLoopBody] := by
  rfl

theorem qsLenGuard_shape :
    qsLenGuard = [.localGet 1, .const 33, .ltU, .br_if 0] := by
  rfl

/-! ## The shape of the quicksort loop -/

theorem qsLoopBody_shape :
    qsLoopBody = .block 0 0 qsHeapArm :: qsAfterHeap := by
  rfl

theorem qsHeapArm_shape :
    qsHeapArm =
      [.localGet 3, .br_if 0, .localGet 0, .localGet 1, .localGet 6,
        .call 25, .br 5] := by
  rfl

theorem qsAfterHeap_split :
    qsAfterHeap =
      qsPivotSetup ++ .block 0 0 qsMedianBlock :: qsAfterMedian := by
  rfl

theorem qsPivotSetup_shape :
    qsPivotSetup =
      [.localGet 0, .localGet 1, .const 3, .shrU, .localTee 6,
        .const 56, .mul, .add, .localSet 7, .localGet 0, .localGet 6,
        .const 5, .shl, .add, .localSet 8] := by
  rfl

theorem qsMedian_split :
    qsMedian =
      qsPivotSetup ++ .block 0 0 qsMedianBlock :: qsLimitDec := by
  rfl

theorem qsMedianBlock_shape :
    qsMedianBlock = .block 0 0 qsMedianCall :: qsMedianInline := by
  rfl

theorem qsMedianCall_shape :
    qsMedianCall =
      [.localGet 1, .const 64, .ltU, .br_if 0, .localGet 0, .localGet 8,
        .localGet 7, .localGet 6, .call 23, .localSet 6, .br 1] := by
  rfl

theorem qsAfterMedian_split :
    qsAfterMedian =
      qsLimitDec ++ .block 0 0 qsPartitionBody :: qsLoopGuard := by
  rfl

theorem qsLimitDec_shape :
    qsLimitDec =
      [.localGet 3, .const 4294967295, .add, .localSet 3, .localGet 6,
        .localGet 0, .sub, .localSet 6] := by
  rfl

theorem qsLoopGuard_shape :
    qsLoopGuard = [.localGet 1, .const 33, .geU, .br_if 0] := by
  rfl

theorem qsPartitionBody_shape :
    qsPartitionBody = .block 0 0 qsEqualPartition :: qsAfterEqual := by
  rfl

/-! ## The shape of the two partitions -/

theorem qsEqualPartition_split :
    qsEqualPartition =
      qsEqualGuard ++ qsEqualSwap ++
        .block 0 0 qsEqualScanFwd :: qsEqualMid ++
          .block 0 0 qsEqualScanBack :: qsEqualWriteBack := by
  rfl

theorem qsEqualScanFwd_split :
    qsEqualScanFwd =
      .block 0 0 qsEqualFwdPre :: qsEqualFwdMid ++
        .loop 0 0 qsEqualFwdLoop :: qsEqualFwdTail := by
  rfl

theorem qsEqualScanBack_split :
    qsEqualScanBack =
      qsEqualBackPre ++
        .loop 0 0 qsEqualBackLoop :: qsEqualBackTail := by
  rfl

theorem qsAfterEqual_split :
    qsAfterEqual = qsStrictPartition ++ qsRecurse := by
  rfl

theorem qsStrictPartition_split :
    qsStrictPartition =
      qsStrictSetup ++ .block 0 0 qsStrictScanFwd :: qsStrictMid ++
        .block 0 0 qsStrictScanBack :: qsStrictWriteBack := by
  rfl

theorem qsStrictScanFwd_split :
    qsStrictScanFwd =
      .block 0 0 qsStrictFwdPre :: qsStrictFwdMid ++
        .loop 0 0 qsStrictFwdLoop :: qsStrictFwdTail := by
  rfl

theorem qsStrictScanBack_split :
    qsStrictScanBack =
      qsStrictBackPre ++
        .loop 0 0 qsStrictBackLoop :: qsStrictBackTail := by
  rfl

/-! ## The shape of the small sort -/

theorem qsAfter4_split :
    qsAfter4 =
      qsSmallSetup ++ .loop 0 0 qsRegionLoop :: qsAfterRegion := by
  rfl

theorem qsSmallSetup_shape :
    qsSmallSetup =
      [.localGet 1, .const 2, .ltU, .br_if 2, .localGet 1, .localGet 1,
        .const 1, .shrU, .localTee 16, .localGet 1, .const 18, .ltU,
        .localTee 17, .select, .localSet 7, .localGet 1, .localGet 16,
        .sub, .localSet 18, .localGet 0, .localGet 16, .const 3, .shl,
        .add, .localSet 13, .localGet 0, .localSet 8] := by
  rfl

theorem qsRegionLoop_shape :
    qsRegionLoop = .block 0 0 qsRegionBody :: qsAfterRegionBody := by
  rfl

theorem qsRegionBody_shape :
    qsRegionBody = .block 0 0 qsNetworkSelect :: qsSort13 := by
  rfl

theorem qsNetworkSelect_split :
    qsNetworkSelect = qsSmallGuard ++ qsSort9 ++ [.br 1] := by
  rfl

theorem qsSmallGuard_shape :
    qsSmallGuard =
      [.localGet 7, .const 12, .gtU, .br_if 0, .const 1, .localSet 6,
        .localGet 7, .const 8, .leU, .br_if 1] := by
  rfl

theorem qsAfterRegionBody_split :
    qsAfterRegionBody =
      qsRegionOrder ++ .block 0 0 qsInsertion :: qsRegionNext := by
  rfl

theorem qsRegionOrder_shape :
    qsRegionOrder = [.localGet 6, .localGet 7, .gtU, .br_if 1] := by
  rfl

theorem qsInsertion_split :
    qsInsertion = qsInsertSetup ++ [.loop 0 0 qsInsertOuter] := by
  rfl

theorem qsInsertOuter_shape :
    qsInsertOuter = .block 0 0 qsInsertCheck :: qsInsertTail := by
  rfl

theorem qsInsertCheck_split :
    qsInsertCheck =
      qsInsertCheckHead ++
        .block 0 0 qsInsertShiftBlock :: qsInsertCheckTail := by
  rfl

theorem qsInsertShiftBlock_shape :
    qsInsertShiftBlock =
      .loop 0 0 qsInsertShift :: qsInsertShiftTail := by
  rfl

theorem qsInsertShift_split :
    qsInsertShift =
      (qsInsertShift.take 9) ++
        .block 0 0 qsInsertInner :: qsInsertShiftBack := by
  rfl

theorem qsRegionNext_shape :
    qsRegionNext =
      [.localGet 17, .br_if 3, .localGet 8, .localGet 0, .eq,
        .localSet 6, .localGet 18, .localSet 7, .localGet 13,
        .localSet 8, .localGet 6, .br_if 0] := by
  rfl

/-! ## The shape of the merge -/

theorem qsAfterRegion_split :
    qsAfterRegion =
      qsMergeSetup ++ .loop 0 0 qsMerge :: qsAfterMerge := by
  rfl

theorem qsMergeSetup_shape :
    qsMergeSetup =
      [.localGet 13, .const 4294967288, .add, .localSet 7, .localGet 0,
        .localGet 1, .const 3, .shl, .const 4294967288, .add,
        .localTee 6, .add, .localSet 8, .localGet 5, .localGet 6, .add,
        .localSet 10, .localGet 5, .localSet 9, .localGet 0,
        .localSet 6] := by
  rfl

theorem qsAfterMerge_split :
    qsAfterMerge = qsMergeMiddle ++ qsPointerCheck ++ qsCopy := by
  rfl

theorem qsMergeMiddle_split :
    qsMergeMiddle = qsMergeAdvance ++ [.block 0 0 qsMergeOdd] := by
  rfl

theorem qsMergeAdvance_shape :
    qsMergeAdvance = [.localGet 7, .const 8, .add, .localSet 7] := by
  rfl

theorem qsPointerCheck_shape :
    qsPointerCheck =
      [.localGet 6, .localGet 7, .ne, .br_if 1, .localGet 13,
        .localGet 8, .const 8, .add, .ne, .br_if 1, .localGet 1,
        .const 3, .shl, .localTee 6, .eqz, .br_if 2] := by
  rfl

theorem qsCopy_shape :
    qsCopy =
      [.localGet 0, .localGet 5, .localGet 6, .memoryCopy, .br 2] := by
  rfl

/-! ## The size of the two sorting networks -/

theorem qsSort9_length : qsSort9.length = 776 := by rfl

theorem qsSort13_length : qsSort13.length = 1381 := by rfl

theorem qsSort9_selects : (qsSort9.filter isSelect).length = 75 := by
  rfl

theorem qsSort13_selects : (qsSort13.filter isSelect).length = 135 := by
  rfl

/-! ## The chunks of the two sorting networks

A chunk holds five comparators, which is 15 `select` instructions.  The
bound of chunk `k` is the instruction index right after the `15 * k`-th
`select`.  The last chunk also takes the three instructions that write
the network result. -/

/-- The chunk bounds of the first network, as instruction indexes into
`qsSort9`.  The WAT lines are 6233, 6414, 6572, 6720, 6866 and 7009. -/
def qsSort9Bound : Nat → Nat
  | 0 => 0
  | 1 => 181
  | 2 => 339
  | 3 => 487
  | 4 => 633
  | _ => 776

/-- Chunk `k` of the first network, for `k < 5`.  The WAT spans are
6233 to 6413, 6414 to 6571, 6572 to 6719, 6720 to 6865 and 6866 to
7008. -/
@[reducible] def qsSort9Chunk (k : Nat) : Program :=
  (qsSort9.drop (qsSort9Bound k)).take
    (qsSort9Bound (k + 1) - qsSort9Bound k)

/-- The chunk bounds of the second network, as instruction indexes into
`qsSort13`.  The WAT lines are 7011, 7201, 7367, 7517, 7665, 7810, 7957,
8103, 8247 and 8392. -/
def qsSort13Bound : Nat → Nat
  | 0 => 0
  | 1 => 190
  | 2 => 356
  | 3 => 506
  | 4 => 654
  | 5 => 799
  | 6 => 946
  | 7 => 1092
  | 8 => 1236
  | _ => 1381

/-- Chunk `k` of the second network, for `k < 9`.  The WAT spans are
7011 to 7200, 7201 to 7366, 7367 to 7516, 7517 to 7664, 7665 to 7809,
7810 to 7956, 7957 to 8102, 8103 to 8246 and 8247 to 8391. -/
@[reducible] def qsSort13Chunk (k : Nat) : Program :=
  (qsSort13.drop (qsSort13Bound k)).take
    (qsSort13Bound (k + 1) - qsSort13Bound k)

theorem qsSort9_chunks :
    qsSort9 =
      qsSort9Chunk 0 ++ qsSort9Chunk 1 ++ qsSort9Chunk 2 ++
        qsSort9Chunk 3 ++ qsSort9Chunk 4 := by
  rfl

theorem qsSort13_chunks :
    qsSort13 =
      qsSort13Chunk 0 ++ qsSort13Chunk 1 ++ qsSort13Chunk 2 ++
        qsSort13Chunk 3 ++ qsSort13Chunk 4 ++ qsSort13Chunk 5 ++
        qsSort13Chunk 6 ++ qsSort13Chunk 7 ++ qsSort13Chunk 8 := by
  rfl

theorem qsSort9Chunk_lengths :
    ((List.range 5).map fun k => (qsSort9Chunk k).length) =
      [181, 158, 148, 146, 143] := by
  rfl

theorem qsSort13Chunk_lengths :
    ((List.range 9).map fun k => (qsSort13Chunk k).length) =
      [190, 166, 150, 148, 145, 147, 146, 144, 145] := by
  rfl

theorem qsSort9Chunk_selects :
    ((List.range 5).map fun k =>
      ((qsSort9Chunk k).filter isSelect).length) =
      [15, 15, 15, 15, 15] := by
  rfl

theorem qsSort13Chunk_selects :
    ((List.range 9).map fun k =>
      ((qsSort13Chunk k).filter isSelect).length) =
      [15, 15, 15, 15, 15, 15, 15, 15, 15] := by
  rfl

/-! ## The control frames

Every block and every loop of the body has no parameter and no result,
and the operand stack below it is empty. -/

/-- One block frame of the body. -/
def qsFrame (body continuation : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := body, continuation := continuation, belowStack := [] }

/-- One loop frame of the body. -/
def qsLoopFrame (body continuation : Program) : ControlFrame :=
  { kind := .loop, paramArity := 0, resultArity := 0,
    body := body, continuation := continuation, belowStack := [] }

/-- The five frames that stand at the head of the quicksort loop `@5`.
The innermost comes first.  `after` is the code that follows the call
of `func 24` in the caller. -/
def qsControlsLoop (after : Program) : List ControlFrame :=
  [qsLoopFrame qsLoopBody [],
    qsFrame qsBlock4Body qsAfter4,
    qsFrame qsBlock3Body qsAfter3,
    qsFrame qsBlock2Body qsAfter2,
    qsFrame qsBlock1Body after]

/-- The four frames that stand at the head of the region loop `@4`. -/
def qsControlsRegion (after : Program) : List ControlFrame :=
  [qsLoopFrame qsRegionLoop [],
    qsFrame qsBlock3Body qsAfter3,
    qsFrame qsBlock2Body qsAfter2,
    qsFrame qsBlock1Body after]

/-! ## The locals

The function takes five arguments and declares 34 more locals, so the
last index is 38.  `Locals` keeps the arguments and the declared locals
apart, so a register name below index 5 sits in `params`. -/

/-- The locals of the body.  `ls` holds the 34 declared locals, in the
order of `Project.RustHashMap.func21Def.locals`, and `vs` holds the
operand stack. -/
@[reducible] def qsLocals (buf len anc limit env : UInt32)
    (ls vs : List Value) : Locals :=
  { params := [.i32 buf, .i32 len, .i32 anc, .i32 limit, .i32 env],
    locals := ls, values := vs }

/-- The 34 declared locals at function entry, all zero. -/
def qsZeroLocals : List Value :=
  [.i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i64 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0,
    .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
    .i64 0, .i64 0]

/-- The locals at function entry, before the frame setup runs. -/
theorem qsZeroLocals_eq (buf len anc limit env : UInt32) :
    Project.RustHashMap.func21Def.toLocals
        [.i32 buf, .i32 len, .i32 anc, .i32 limit, .i32 env] =
      qsLocals buf len anc limit env qsZeroLocals [] := by
  rfl

/-- The locals after the frame setup of WAT 5672 to 5676.  Local 5 holds
the frame pointer and every other declared local still holds zero. -/
def func21_initialLocals (buf len anc limit env fp : UInt32) : Locals :=
  qsLocals buf len anc limit env
    (.i32 fp :: qsZeroLocals.drop 1) []

theorem func21_initialLocals_locals (buf len anc limit env fp : UInt32) :
    (func21_initialLocals buf len anc limit env fp).locals =
      [.i32 fp, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i64 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i64 0, .i32 0, .i64 0, .i32 0,
        .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0,
        .i64 0, .i64 0] := by
  rfl

end Project.RustHashMap.Func21Defs
