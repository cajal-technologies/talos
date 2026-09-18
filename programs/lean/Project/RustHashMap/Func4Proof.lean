import Project.RustHashMap.EntriesContracts
import Project.RustHashMap.Func11Proof
import Project.RustHashMap.Func12Proof
import Project.RustHashMap.Func21Proof
import Project.RustHashMap.Func55Proof
import Project.RustHashMap.Func30Proof
import Project.RustHashMap.LookupPures
import Project.RustHashMap.FrameCells
import CodeLib.RustStd.HashMap.EraseWasm

/-!
# Proof of `sorted_entries`, absolute `func 7`

This file proves local `func4`, absolute `func 7`, against
`Project.RustHashMap.EntriesContracts.Func4Spec`.  The body is WAT lines
1022 to 1299 of `programs/rust/build/rust_hash_map/program.wat`.

The body walks the control bytes of the table one group of eight at a
time, copies every full bucket into a fresh buffer in ascending bucket
order, and sorts that buffer by key.

## The two loops

The walk loop, WAT 1157 to 1175, steps the group pointer by eight and the
slot base by 64 until a group reports a full bucket.  `walkRest` is the
list of buckets that the walk still has to report, and `walkRest_step`
says that one step of that loop keeps it.

The push loop, WAT 1151 to 1246, writes one entry per turn.  Its index
`len` counts the entries already written and its counter `left` counts
the turns that remain.  The invariant is `len + left = t.items` together
with `(fullIndices t).take len ++ walkRest t b m = fullIndices t`.

## The dead arms

X-F7-CAP is the `call 99` and `unreachable` at WAT 1285, behind the two
guards at WAT 1084 to 1091.  `t.buckets <= 2 ^ 27` bounds `t.items` by
`2 ^ 27`, so the capacity is at most `2 ^ 27` and eight times it is at
most `2 ^ 30`.  Both guards are false.

X-F7-GROW is the `call 13` at WAT 1215, behind the guard at WAT 1203 to
1207, which compares the loop index with the capacity.  The push-loop
invariant gives `len < t.items <= cap`, so the guard is false.

X-F7-NULL is the same `call 99` at WAT 1285, reached from the guard at
WAT 1117 to 1120 after `call 58`.  A live block never starts at address
zero, so the guard is false.

## The empty table

The guard at WAT 1031 to 1035 leaves the outer block when the item count
is zero, and the arm at WAT 1288 to 1293 writes the capacity 0, the
dangling pointer 4 and the count 0.  That arm allocates nothing and never
reaches the sort dispatch at WAT 1265, so `Func12Spec` always gets a
buffer of two entries or more.
-/

namespace Project.RustHashMap.Func4Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.SortContracts
open Project.RustHashMap.GrowContract
open Project.RustHashMap.PairGrow
open Project.RustHashMap.VecGrow
open Project.RustHashMap.EntriesContracts
open scoped Wasm.SmallStep.Outcome

/-! ## The shape of the compiled body -/

/-- `repeat(0x80)` as the compiled code writes it. -/
@[reducible] private def rep80 : UInt64 := Table.REP80

/-! ## Two call bridges

`iapply` needs an entailment whose head is the turnstile.  `CallContract`
hides that head behind a definition, and the two specs below give the
same statements in the open form.  Neither adds an assumption. -/

/-- `Func30Spec` in the open form.  The marker function takes no operand
and gives none back. -/
private theorem marker_call [WasmSmallStepGS hlc Universal.State]
    (callerLocals : Locals) {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗
      (RuntimeContext -∗ ResumeWP [] callerLocals stack code arity
        remainder controls calls s E Φ)) ⊢
      WP (.running ⟨{ callerLocals with values := stack },
        .call 33 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] :=
  Project.RustHashMap.Func30Proof.func30_correct (hlc := hlc)

/-- `Func55Spec` in the open form.  The allocator takes the alignment and
then the size. -/
private theorem alloc_call [WasmSmallStepGS hlc Universal.State]
    (callerLocals : Locals) (size alignment : UInt32)
    (layout : AllocLayout) (heapId : GName) (storedCursor : UInt32)
    (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ⌜layout.Matches size alignment ∧ layout.Valid ∧
        (layout.alignment = 1 ∨ layout.alignment = 4)⌝ ∗
      AllocContinuation heapId storedCursor frontier history layout
        input output raised callerLocals stack code arity remainder
        controls calls s E Φ) ⊢
      WP (.running ⟨{ callerLocals with
            values := .i32 alignment :: .i32 size :: stack },
        .call 58 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] :=
  Project.RustHashMap.Func55Proof.func55_correct (hlc := hlc) size
    alignment layout heapId storedCursor frontier history input output
    raised

/-- `Func12Spec` in the open form.  The operands are the buffer, then
the length, then the offset. -/
private theorem sort15_call [WasmSmallStepGS hlc Universal.State]
    (callerLocals : Locals) (v len offset : UInt32)
    (pairs : List (UInt32 × UInt32))
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗
      Table.PairSlice 0 v pairs ∗
      ⌜pairs.length = len.toNat ∧ 1 ≤ offset.toNat ∧
        offset.toNat ≤ len.toNat ∧
        Table.SortedByKey (pairs.take offset.toNat) ∧
        v.toNat + 8 * len.toNat < UInt32.size⌝ ∗
      SortPostFrameless v pairs callerLocals stack code arity remainder
        controls calls s E Φ) ⊢
      WP (.running ⟨{ callerLocals with
            values := .i32 offset :: .i32 len :: .i32 v :: stack },
        .call 15 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] :=
  Project.RustHashMap.Func12Proof.func12_correct (hlc := hlc) v len offset
    pairs

/-- `Func11Spec` in the open form.  The operands are the buffer, then the
length, then the comparison closure. -/
private theorem sort14_call [WasmSmallStepGS hlc Universal.State]
    (callerLocals : Locals) (sp v len env : UInt32)
    (pairs : List (UInt32 × UInt32)) (below : List UInt8)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(RuntimeContext ∗
      StackPointer sp ∗
      StackBelow sp (sortDepth len.toNat) below ∗
      Table.PairSlice 0 v pairs ∗
      ⌜pairs.length = len.toNat ∧ Wasm.RustStd.HashMap.NodupKeys pairs ∧
        len.toNat ≤ 2 ^ 27 ∧
        v.toNat + 8 * len.toNat < UInt32.size ∧
        sortDepth len.toNat ≤ sp.toNat⌝ ∗
      SortPost v pairs sp (sortDepth len.toNat) iprop(emp) callerLocals
        stack code arity remainder controls calls s E Φ) ⊢
      WP (.running ⟨{ callerLocals with
            values := .i32 env :: .i32 len :: .i32 v :: stack },
        .call 14 :: code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] :=
  Project.RustHashMap.Func11Proof.func11_correct_of (hlc := hlc)
    Project.RustHashMap.Func21Proof.func21_correct sp v len env pairs below

/-- The group advance of the walk, WAT 1158 to 1174 and WAT 1052 to
1068. -/
@[reducible] private def advLoop : Program :=
  [.localGet 4, .localTee 6, .const 8, .add, .localSet 4, .localGet 1,
    .const 4294967232, .add, .localSet 1, .localGet 6, .load64 0,
    .constI64 rep80, .andI64, .localTee 5, .constI64 rep80, .eqI64,
    .br_if 0]

/-- The first group test and the advance, WAT 1043 to 1069. -/
@[reducible] private def peelBlock : Program :=
  [.localGet 1, .load64 0, .constI64 rep80, .andI64, .localTee 5,
    .constI64 rep80, .neI64, .br_if 0, .loop 0 0 advLoop]

/-- The refill of the group mask inside the push loop, WAT 1153 to
1179. -/
@[reducible] private def maskBlock : Program :=
  [.localGet 5, .constI64 0, .neI64, .br_if 0, .loop 0 0 advLoop,
    .localGet 5, .constI64 rep80, .xorI64, .localSet 5]

/-- The dead grow arm of the push loop, WAT 1203 to 1218. -/
@[reducible] private def growBlock : Program :=
  [.localGet 3, .localGet 2, .load32 4, .ne, .br_if 0, .localGet 2,
    .const 4, .add, .localGet 3, .localGet 8, .const 4, .const 8,
    .call 13, .localGet 2, .load32 8, .localSet 11]

/-- One turn of the push loop, WAT 1152 to 1245. -/
@[reducible] private def pushLoop : Program :=
  [.block 0 0 maskBlock, .localGet 5, .constI64 18446744073709551615,
    .addI64, .localSet 12, .localGet 1, .localGet 5, .ctzI64, .wrapI64,
    .const 120, .and, .sub, .localTee 6, .const 4294967292, .add,
    .load32 0, .localSet 7, .localGet 6, .const 4294967288, .add,
    .load32 0, .localSet 6, .block 0 0 growBlock, .localGet 12,
    .localGet 5, .andI64, .localSet 5, .localGet 11, .localGet 3,
    .const 3, .shl, .add, .localTee 9, .localGet 7, .store32 4,
    .localGet 9, .localGet 6, .store32 0, .localGet 2, .localGet 3,
    .const 1, .add, .localTee 3, .store32 12, .localGet 8,
    .const 4294967295, .add, .localTee 8, .br_if 0]

/-- The entry count test and the push loop, WAT 1137 to 1246. -/
@[reducible] private def pushBlock : Program :=
  [.localGet 3, .const 4294967295, .add, .localTee 8, .eqz, .br_if 0,
    .localGet 5, .constI64 18446744073709551615, .addI64, .localGet 5,
    .andI64, .localSet 5, .const 1, .localSet 3, .loop 0 0 pushLoop]

/-- The dispatch of the sort, WAT 1265 to 1275. -/
@[reducible] private def sortBlock : Program :=
  [.localGet 1, .const 21, .ltU, .br_if 0, .localGet 4, .localGet 1,
    .localGet 2, .const 4, .add, .call 14, .br 3]

/-- The header stores and the sort dispatch, WAT 1248 to 1281. -/
@[reducible] private def sortTail : Program :=
  [.localGet 0, .localGet 2, .load64 4, .store64 0, .localGet 0,
    .localGet 2, .load32 12, .localTee 1, .store32 8, .localGet 1,
    .const 2, .ltU, .br_if 2, .localGet 0, .load32 4, .localSet 4,
    .block 0 0 sortBlock, .localGet 4, .localGet 1, .const 1, .call 15,
    .br 2]

/-- The first entry, the allocation and the push loop, WAT 1084 to
1281. -/
@[reducible] private def mainBlock : Program :=
  .localGet 3 :: .const 536870911 :: .gtU :: .br_if 0 :: .localGet 6 ::
    .const 2147483644 :: .gtU :: .br_if 0 :: .localGet 1 :: .localGet 5 ::
    .constI64 rep80 :: .xorI64 :: .localTee 5 :: .ctzI64 :: .wrapI64 ::
    .const 120 :: .and :: .sub :: .localTee 8 :: .const 4294967292 ::
    .add :: .load32 0 :: .localSet 9 :: .localGet 8 ::
    .const 4294967288 :: .add :: .load32 0 :: .localSet 10 :: .call 33 ::
    .const 4 :: .localSet 8 :: .localGet 6 :: .const 4 :: .call 58 ::
    .localTee 11 :: .eqz :: .br_if 0 :: .localGet 11 :: .localGet 9 ::
    .store32 4 :: .localGet 11 :: .localGet 10 :: .store32 0 ::
    .localGet 2 :: .const 1 :: .store32 12 :: .localGet 2 ::
    .localGet 11 :: .store32 8 :: .localGet 2 :: .localGet 7 ::
    .store32 4 :: .block 0 0 pushBlock :: sortTail

/-- The capacity, the two guards and the out-of-memory arm, WAT 1071 to
1286. -/
@[reducible] private def capTail : Program :=
  [.localGet 3, .const 4, .localGet 3, .const 4, .gtU, .select,
    .localTee 7, .const 3, .shl, .localSet 6, .const 0, .localSet 8,
    .block 0 0 mainBlock, .localGet 8, .localGet 6, .call 99,
    .unreachable]

/-- The whole of the block that the empty table leaves, WAT 1031 to
1286. -/
@[reducible] private def body2 : Program :=
  .localGet 1 :: .load32 12 :: .localTee 3 :: .eqz :: .br_if 0 ::
    .localGet 1 :: .load32 0 :: .localTee 1 :: .const 8 :: .add ::
    .localSet 4 :: .block 0 0 peelBlock :: capTail

/-- The block that every exit leaves, WAT 1030 to 1293. -/
@[reducible] private def body1 : Program :=
  [.block 0 0 body2, .localGet 0, .const 0, .store32 8, .localGet 0,
    .constI64 17179869184, .store64 0]

/-- The epilogue, WAT 1295 to 1298. -/
@[reducible] private def epilogue : Program :=
  [.localGet 2, .const 16, .add, .globalSet 0]

/-- The control frame of the block that holds the push loop. -/
@[reducible] private def pushFrame : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0, body := pushBlock,
    continuation := sortTail, belowStack := [] }

/-- The three control frames that hold the body of `sorted_entries` when
the sort dispatch runs. -/
@[reducible] private def tailFrames : List ControlFrame :=
  [{ kind := .block, paramArity := 0, resultArity := 0,
      body := mainBlock,
      continuation := [.localGet 8, .localGet 6, .call 99, .unreachable],
      belowStack := [] },
    { kind := .block, paramArity := 0, resultArity := 0, body := body2,
      continuation := [.localGet 0, .const 0, .store32 8, .localGet 0,
        .constI64 17179869184, .store64 0],
      belowStack := [] },
    { kind := .block, paramArity := 0, resultArity := 0, body := body1,
      continuation := epilogue, belowStack := [] }]

set_option maxRecDepth 1048576 in
/-- The generated body is the frame, one block and the epilogue. -/
private theorem func4_shape :
    Project.RustHashMap.func4 =
      .globalGet 0 :: .const 16 :: .sub :: .localTee 2 :: .globalSet 0 ::
        .block 0 0 body1 :: epilogue := rfl

private theorem func4_index :
    Project.RustHashMap.«module».funcs[4]? =
      some Project.RustHashMap.func4Def := by rfl

/-! ## The order of the walk

The walk reads one group of eight control bytes at a time and reports the
full buckets of that group from the lowest byte up.  `groupIdx` is the
list of buckets that one group reports, and `walkRest` is the list that
the walk still has to report from a residual mask and the groups after
it. -/

/-- `~group & REP80`, as the compiled code writes it: the group word is
masked first and the mask is flipped afterwards. -/
private theorem full_of_and_xor (g : UInt64) :
    (g &&& Table.REP80) ^^^ Table.REP80 = Table.swarMatchFull g := by
  unfold Table.swarMatchFull
  rw [← UInt64.toBitVec_inj]
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_and, BitVec.getElem_not,
    UInt64.toBitVec_xor, UInt64.toBitVec_and, UInt64.toBitVec_not]
  cases hg : g.toBitVec[i] <;> cases hr : Table.REP80.toBitVec[i] <;> simp

/-- The buckets that group `b` reports, in ascending order. -/
private def groupIdx (t : Table UInt32 UInt32) (b : Nat) : List Nat :=
  (Table.setBytes
      (Table.swarMatchFull
        (Table.groupWord (Table.groupAt t (8 * b))))).map
    (fun j => 8 * b + j)

/-- The number of groups that the walk loads.  A table of one or four
buckets has one group, whose pad bytes are `EMPTY`. -/
private def numGroups (t : Table UInt32 UInt32) : Nat :=
  if t.buckets < 8 then 1 else t.buckets / 8

/-- The buckets that the walk still has to report: the residual mask of
group `b`, then every group after it. -/
private def walkRest (t : Table UInt32 UInt32) (b : Nat) (m : UInt64) :
    List Nat :=
  (Table.setBytes m).map (fun j => 8 * b + j) ++
    (List.range' (b + 1) (numGroups t - (b + 1))).flatMap (groupIdx t)

private theorem setBytes_zero : Table.setBytes 0 = [] := by decide

/-- A table of eight buckets or more has a bucket count that eight
divides. -/
private theorem eight_dvd_buckets {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.Layout hash t)
    (hb : 8 ≤ t.buckets) : t.buckets = 8 * (t.buckets / 8) := by
  obtain ⟨e, -, -, hbe⟩ := hw.shape
  have hthree : 3 ≤ e := by
    by_contra hlt
    interval_cases e <;> omega
  have hdvd : (8 : Nat) ∣ t.buckets := by
    rw [hbe]
    exact Nat.pow_dvd_pow 2 hthree
  omega

/-- The groups of the walk report exactly `Table.fullIndices`, in the
ascending order that the model folds over. -/
private theorem groups_eq_fullIndices {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.Layout hash t) :
    (List.range (numGroups t)).flatMap (groupIdx t) =
      Table.fullIndices t := by
  unfold numGroups
  by_cases hb : t.buckets < 8
  · rw [if_pos hb]
    simp only [List.range_one, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, groupIdx, Nat.mul_zero, Nat.zero_add]
    rw [Table.walk_eq_fullIndices_small hw hb, List.map_id_fun']
    rfl
  · rw [if_neg hb]
    exact Table.walk_eq_fullIndices t (eight_dvd_buckets hw (by omega))

/-- Group `b` of the walk lies inside the control bytes. -/
private theorem group_room {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.Layout hash t) {b : Nat}
    (hb : b < numGroups t) : 8 * b + 8 ≤ t.ctrl.length := by
  rw [hw.ctrl_len]
  unfold numGroups at hb
  by_cases hsmall : t.buckets < 8
  · rw [if_pos hsmall] at hb
    omega
  · rw [if_neg hsmall] at hb
    have hdvd := eight_dvd_buckets hw (by omega)
    omega

/-- One turn of the group advance keeps the list the walk still owes.  The
next group is loaded and its mask becomes the residual one. -/
private theorem walkRest_step (t : Table UInt32 UInt32) {b : Nat}
    (hb : b + 1 < numGroups t) :
    walkRest t (b + 1)
        (Table.swarMatchFull
          (Table.groupWord (Table.groupAt t (8 * (b + 1))))) =
      walkRest t b 0 := by
  unfold walkRest
  rw [setBytes_zero]
  simp only [List.map_nil, List.nil_append]
  have hcount : numGroups t - (b + 1) = (numGroups t - (b + 2)) + 1 := by
    omega
  rw [hcount]
  simp only [List.range'_succ, List.flatMap_cons, groupIdx]

/-! ## Small word bridges -/

private theorem addNegSixtyFour (x : UInt32) : x + 4294967232 = x - 64 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967232 : UInt32).toNat = 4294967232 from rfl,
    show (64 : UInt32).toNat = 64 from rfl] at *
  omega

/-- `x ^^^ y` is zero exactly when the two words agree. -/
private theorem xor_eq_zero_iff (x y : UInt64) : x ^^^ y = 0 ↔ x = y := by
  constructor
  · intro h
    have hstep := congrArg (fun z => z ^^^ y) h
    simp only [UInt64.xor_assoc, UInt64.xor_self, UInt64.xor_zero,
      UInt64.zero_xor] at hstep
    exact hstep
  · rintro rfl
    exact UInt64.xor_self

/-- The residual mask keeps the `REP80` shape under the iterator step. -/
private theorem iterNext_and_REP80 {m : UInt64}
    (hm : m &&& Table.REP80 = m) :
    (m &&& (m + 18446744073709551615)) &&& Table.REP80 =
      m &&& (m + 18446744073709551615) := by
  rw [UInt64.and_assoc, UInt64.and_comm (m + 18446744073709551615),
    ← UInt64.and_assoc, hm]

/-- One entry of the walk: the lowest flagged byte of the residual mask
comes first, and the rest follows the iterator step. -/
private theorem walkRest_pop (t : Table UInt32 UInt32) {b : Nat}
    {m : UInt64} (hm : m &&& Table.REP80 = m) (hne : m ≠ 0) :
    walkRest t b m =
      (8 * b + ctz64 64 m / 8) ::
        walkRest t b (m &&& (m + 18446744073709551615)) := by
  unfold walkRest
  rw [Table.setBytes_iterNext hm (Table.lowestSetByte_eq_ctz hm hne)]
  simp only [List.map_cons, List.cons_append]

/-- With an empty residual mask and buckets still to report, one more
group follows. -/
private theorem next_group_of_ne_nil (t : Table UInt32 UInt32) {b : Nat}
    (hne : walkRest t b 0 ≠ []) : b + 1 < numGroups t := by
  by_contra hge
  apply hne
  unfold walkRest
  rw [setBytes_zero, show numGroups t - (b + 1) = 0 by omega]
  rfl

/-- The walk starts at group zero with the mask of that group. -/
private theorem walkRest_start {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.Layout hash t) :
    walkRest t 0
        (Table.swarMatchFull (Table.groupWord (Table.groupAt t 0))) =
      Table.fullIndices t := by
  have hpos : 0 < numGroups t := by
    unfold numGroups
    split <;> omega
  rw [← groups_eq_fullIndices hw, List.range_eq_range',
    show numGroups t = (numGroups t - 1) + 1 by omega,
    List.range'_succ]
  simp only [List.flatMap_cons, groupIdx, walkRest, Nat.mul_zero,
    Nat.zero_add]

private theorem negSixtyFourAdd (x : UInt32) :
    4294967232 + x = x - 64 := by
  rw [UInt32.add_comm]
  exact addNegSixtyFour x

/-- The slot base of the next group. -/
private theorem slotBase_step (ctrl : UInt32) (b : Nat) :
    4294967232 + (ctrl - UInt32.ofNat (64 * b))
      = ctrl - UInt32.ofNat (64 * (b + 1)) := by
  rw [negSixtyFourAdd, show (64 : UInt32) = UInt32.ofNat 64 from rfl,
    sub_sub_ofNat, show 64 * b + 64 = 64 * (b + 1) by omega]

/-- The address of the group word after the next one. -/
private theorem nextGroup_step (ctrl : UInt32) (b : Nat) :
    8 + (ctrl + UInt32.ofNat (8 * (b + 1)))
      = ctrl + UInt32.ofNat (8 * (b + 1 + 1)) := by
  rw [show 8 * (b + 1 + 1) = 8 * (b + 1) + 8 by omega, UInt32.ofNat_add,
    show UInt32.ofNat 8 = (8 : UInt32) from rfl, ← UInt32.add_assoc,
    UInt32.add_comm (8 : UInt32), UInt32.add_assoc,
    UInt32.add_comm (8 : UInt32)]

/-- Move an owned double word between two names of one address.  Copy of
`Func15Insert.wordMove64`. -/
private theorem wordMove64 [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {value : UInt64}
    (haddress : address = address') :
    pointsTo_u64 0 address value ⊢ pointsTo_u64 0 address' value := by
  rw [haddress]

/-! ## The group advance

WAT 1051 to 1069 and WAT 1157 to 1175 hold the same loop.  It steps the
group pointer by eight bytes and the slot base by 64 bytes until a group
reports a full bucket. -/

/-- The registers of absolute `func 7` at the head of either walk.  Local
0 is the output slot and local 1 is the slot base of the current group.
Local 2 is the frame, local 3 the item count, local 4 the address of the
next group word and local 5 the group mask. -/
@[reducible] private def walkLocals (out slotBase frame items next : UInt32)
    (m : UInt64) (l6 l7 l8 l9 l10 l11 : UInt32) (l12 : UInt64) : Locals :=
  { params := [Value.i32 out, .i32 slotBase],
    locals := [.i32 frame, .i32 items, .i32 next, .i64 m, .i32 l6,
      .i32 l7, .i32 l8, .i32 l9, .i32 l10, .i32 l11, .i64 l12],
    values := [] }

set_option maxHeartbeats 2000000 in
/-- The group advance.  It ends at the first group after `b` whose mask
reports a full bucket, and the buckets that the walk still owes do not
change. -/
private theorem twp_advance [WasmSmallStepGS hlc Universal.State]
    {hash : UInt32 → UInt64} {t : Table UInt32 UInt32}
    (hw : Table.Layout hash t) (ctrl : UInt32) (target : List Nat)
    {out frame items l6 l7 l8 l9 l10 l11 : UInt32} {mAny l12 : UInt64}
    {b : Nat} {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (htarget : walkRest t b 0 = target) (hne : target ≠ []) :
    iprop(
      Slices.ByteSlice 0 ctrl t.ctrl ∗
      (∀ (b' : Nat) (l6' : UInt32),
        ⌜b' < numGroups t ∧
          walkRest t b'
              (Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * b')))) = target ∧
          Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b'))) ≠ 0⌝ -∗
        Slices.ByteSlice 0 ctrl t.ctrl -∗
        WP (.running
            ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b')) frame items
                (ctrl + UInt32.ofNat (8 * (b' + 1)))
                (Table.groupWord (Table.groupAt t (8 * b')) &&&
                  Table.REP80)
                l6' l7 l8 l9 l10 l11 l12,
              rest, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b)) frame items
              (ctrl + UInt32.ofNat (8 * (b + 1))) mAny l6 l7 l8 l9 l10 l11
              l12,
            .loop 0 0 advLoop :: rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hctrl, Hexit⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat × UInt64 × UInt32)
    (measure := fun i => numGroups t - i.1)
    (locals := fun i =>
      walkLocals out (ctrl - UInt32.ofNat (64 * i.1)) frame items
        (ctrl + UInt32.ofNat (8 * (i.1 + 1))) i.2.1 i.2.2 l7 l8 l9 l10 l11
        l12)
    (I := fun i => iprop(
      ⌜walkRest t i.1 0 = target⌝ ∗
      Slices.ByteSlice 0 ctrl t.ctrl ∗
      (∀ (b' : Nat) (l6' : UInt32),
        ⌜b' < numGroups t ∧
          walkRest t b'
              (Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * b')))) = target ∧
          Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b'))) ≠ 0⌝ -∗
        Slices.ByteSlice 0 ctrl t.ctrl -∗
        WP (.running
            ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b')) frame items
                (ctrl + UInt32.ofNat (8 * (b' + 1)))
                (Table.groupWord (Table.groupAt t (8 * b')) &&&
                  Table.REP80)
                l6' l7 l8 l9 l10 l11 l12,
              rest, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])))
    (initial := (b, mAny, l6))
    (initialLocals := walkLocals out (ctrl - UInt32.ofNat (64 * b)) frame
      items (ctrl + UInt32.ofNat (8 * (b + 1))) mAny l6 l7 l8 l9 l10 l11
      l12)
    rfl rfl
  · rintro ⟨b0, m0, l60⟩
    iintro Hrec ⟨%htgt, Hctrl, Hexit⟩
    have hnextGroup : b0 + 1 < numGroups t :=
      next_group_of_ne_nil t (by rw [htgt]; exact hne)
    have hroom : 8 * (b0 + 1) + 8 ≤ t.ctrl.length := group_room hw hnextGroup
    have hkeep := walkRest_step t hnextGroup
    simp only [Wasm.SmallStep.loopBodyExpr, advLoop, walkLocals, rep80]
    ihave ⟨Hpre, ⟨%hgbound, Hword⟩, Hpost⟩ :=
      (Table.ByteSlice_groupAt 0 ctrl t hroom).mp $$ Hctrl
    have hfacts := offset_facts64 (ctrl + UInt32.ofNat (8 * (b0 + 1))) 0 0
      rfl (by omega)
    wasm_twp_pures [twp_localGet]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_add]
    isimp only [nextGroup_step]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    isimp only [slotBase_step]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    ihave Hword := wordMove64 (UInt32.add_zero _).symm $$ Hword
    wasm_twp_rebind Wasm.SmallStep.twp_load64
      (address := ctrl + UInt32.ofNat (8 * (b0 + 1))) (offset := 0)
      (Table.groupWord (Table.groupAt t (8 * (b0 + 1)))) hfacts.1
      hfacts.2.1 hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1
      hfacts.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2
      with Hword
    ihave Hword := wordMove64 (UInt32.add_zero _) $$ Hword
    ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hpre Hword Hpost]
    · iapply (Table.ByteSlice_groupAt 0 ctrl t hroom).mpr
      isplitl_exact Hpre
      · isplitl [Hword]
        · isplitl_pureexact hgbound
          · iexact Hword
        · iexact Hpost
    wasm_twp_pures [twp_constI64 twp_andI64_bits]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_constI64]
    by_cases hfull :
        Table.groupWord (Table.groupAt t (8 * (b0 + 1))) &&& Table.REP80 =
          Table.REP80
    · -- the group holds no full bucket: take one more turn
      have hzero :
          Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * (b0 + 1)))) = 0 := by
        rw [← full_of_and_xor, hfull]
        exact UInt64.xor_self
      have hkeep0 : walkRest t (b0 + 1) 0 = walkRest t b0 0 := by
        rw [← hkeep, hzero]
      iapply Wasm.SmallStep.twp_eqI64 (result := 1) (by rw [if_pos hfull])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hback := Hrec
        $$ %((b0 + 1,
            Table.groupWord (Table.groupAt t (8 * (b0 + 1))) &&&
              Table.REP80,
            ctrl + UInt32.ofNat (8 * (b0 + 1))) : Nat × UInt64 × UInt32)
          %(by simp only []; omega)
      iapply Hback
      isplitl_pureexact (show walkRest t (b0 + 1) 0 = target by
        rw [hkeep0]; exact htgt)
      · iframe Hctrl Hexit
    · -- the group holds a full bucket: leave the loop
      have hne0 :
          Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * (b0 + 1)))) ≠ 0 := by
        rw [← full_of_and_xor]
        intro hc
        exact hfull ((xor_eq_zero_iff _ _).mp hc)
      iapply Wasm.SmallStep.twp_eqI64 (result := 0) (by rw [if_neg hfull])
      wasm_twp_pures [twp_brIfZero twp_exitControl]
      simp only [List.take_zero, List.nil_append, List.drop_zero]
      ihave Hgo := Hexit $$ %(b0 + 1) %(ctrl + UInt32.ofNat (8 * (b0 + 1)))
        %(⟨hnextGroup, by rw [hkeep]; exact htgt, hne0⟩ :
          b0 + 1 < numGroups t ∧
            walkRest t (b0 + 1)
                (Table.swarMatchFull
                  (Table.groupWord (Table.groupAt t (8 * (b0 + 1))))) =
              target ∧
            Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * (b0 + 1)))) ≠ 0)
        Hctrl
      iexact Hgo
  · isplitl_pureexact htarget
    · iframe Hctrl Hexit

/-! ## The first group test

WAT 1042 to 1070 tests group zero and then runs the advance. -/

set_option maxHeartbeats 2000000 in
/-- The peel of the walk.  It ends at the first group whose mask reports a
full bucket, which is group zero when that group already has one. -/
private theorem twp_peel [WasmSmallStepGS hlc Universal.State]
    {hash : UInt32 → UInt64} {t : Table UInt32 UInt32}
    (hw : Table.Layout hash t) (ctrl : UInt32) (target : List Nat)
    {out frame items l6 l7 l8 l9 l10 l11 : UInt32} {mAny l12 : UInt64}
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hstart : walkRest t 0
        (Table.swarMatchFull (Table.groupWord (Table.groupAt t 0))) =
      target)
    (hne : target ≠ []) :
    iprop(
      Slices.ByteSlice 0 ctrl t.ctrl ∗
      (∀ (b' : Nat) (l6' : UInt32),
        ⌜b' < numGroups t ∧
          walkRest t b'
              (Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * b')))) = target ∧
          Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b'))) ≠ 0⌝ -∗
        Slices.ByteSlice 0 ctrl t.ctrl -∗
        WP (.running
            ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b')) frame items
                (ctrl + UInt32.ofNat (8 * (b' + 1)))
                (Table.groupWord (Table.groupAt t (8 * b')) &&&
                  Table.REP80)
                l6' l7 l8 l9 l10 l11 l12,
              rest, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨walkLocals out ctrl frame items (8 + ctrl) mAny l6 l7 l8 l9 l10
              l11 l12,
            .block 0 0 peelBlock :: rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hctrl, Hexit⟩
  have hbase0 : ctrl - UInt32.ofNat (64 * 0) = ctrl := by
    simp only [Nat.mul_zero, show UInt32.ofNat 0 = (0 : UInt32) from rfl,
      UInt32.sub_zero]
  have hnext0 : ctrl + UInt32.ofNat (8 * (0 + 1)) = 8 + ctrl := by
    rw [show 8 * (0 + 1) = 8 from rfl,
      show UInt32.ofNat 8 = (8 : UInt32) from rfl, UInt32.add_comm]
  rw [show walkLocals out ctrl frame items (8 + ctrl) mAny l6 l7 l8 l9 l10
        l11 l12
      = walkLocals out (ctrl - UInt32.ofNat (64 * 0)) frame items
          (ctrl + UInt32.ofNat (8 * (0 + 1))) mAny l6 l7 l8 l9 l10 l11 l12
    from by rw [hbase0, hnext0]]
  have hpos : 0 < numGroups t := by
    unfold numGroups
    split <;> omega
  have hroom : 0 + 8 ≤ t.ctrl.length := by
    have hr := group_room hw hpos
    omega
  have hzero : UInt32.ofNat 0 = (0 : UInt32) := rfl
  have hbase : ctrl - UInt32.ofNat (64 * 0) = ctrl := by
    simp only [Nat.mul_zero, hzero, UInt32.sub_zero]
  have hzaddr : ctrl + UInt32.ofNat 0
      = ctrl - UInt32.ofNat (64 * 0) + 0 := by
    simp only [hzero, UInt32.add_zero, Nat.mul_zero, UInt32.sub_zero]
  ihave ⟨Hpre, ⟨%hgbound, Hword⟩, Hpost⟩ :=
    (Table.ByteSlice_groupAt 0 ctrl t hroom).mp $$ Hctrl
  have hfacts := offset_facts64 (ctrl - UInt32.ofNat (64 * 0)) 0 0 rfl
    (by
      rw [hbase]
      simp only [hzero, UInt32.add_zero] at hgbound
      omega)
  simp only [peelBlock, walkLocals, rep80]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_localGet]
  ihave Hword := wordMove64 hzaddr $$ Hword
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := ctrl - UInt32.ofNat (64 * 0)) (offset := 0)
    (Table.groupWord (Table.groupAt t 0)) hfacts.1 hfacts.2.1
    hfacts.2.2.1 hfacts.2.2.2.1 hfacts.2.2.2.2.1 hfacts.2.2.2.2.2.1
    hfacts.2.2.2.2.2.2.1 hfacts.2.2.2.2.2.2.2 with Hword
  ihave Hword := wordMove64 hzaddr.symm $$ Hword
  ihave Hctrl : Slices.ByteSlice 0 ctrl t.ctrl $$ [Hpre Hword Hpost]
  · iapply (Table.ByteSlice_groupAt 0 ctrl t hroom).mpr
    isplitl_exact Hpre
    · isplitl [Hword]
      · isplitl_pureexact hgbound
        · iexact Hword
      · iexact Hpost
  wasm_twp_pures [twp_constI64 twp_andI64_bits]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64]
  by_cases hfull :
      Table.groupWord (Table.groupAt t 0) &&& Table.REP80 = Table.REP80
  · -- group zero holds no full bucket: run the advance
    have hzeroFull :
        Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)) = 0 := by
      rw [← full_of_and_xor, hfull]
      exact UInt64.xor_self
    iapply Wasm.SmallStep.twp_neI64 (result := 0) (by rw [if_neg (by
      simpa using hfull)])
    wasm_twp_pures [twp_brIfZero]
    iapply twp_advance hw ctrl target (b := 0) (mAny :=
        Table.groupWord (Table.groupAt t 0) &&& Table.REP80)
      (by rw [← hstart, hzeroFull]) hne
    isplitl_exact Hctrl
    · iintro %b' %l6' %hb' Hctrl
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      ihave Hgo := Hexit $$ %b' %l6' %hb' Hctrl
      iexact Hgo
  · -- group zero holds a full bucket: leave the block at once
    have hneFull :
        Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)) ≠ 0 := by
      rw [← full_of_and_xor]
      intro hc
      exact hfull ((xor_eq_zero_iff _ _).mp hc)
    iapply Wasm.SmallStep.twp_neI64 (result := 1) (by rw [if_pos (by
      simpa using hfull)])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave Hgo := Hexit $$ %0 %l6
      %(⟨hpos, hstart, hneFull⟩ :
        0 < numGroups t ∧
          walkRest t 0
              (Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * 0)))) = target ∧
          Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * 0))) ≠ 0)
      Hctrl
    iexact Hgo

/-! ## The mask refill of the push loop

WAT 1152 to 1180.  The loop keeps the residual mask of the current group
and refills it from the next group that reports a full bucket. -/

set_option maxHeartbeats 2000000 in
/-- The refill block.  It ends with a mask that flags at least one full
bucket and that keeps the list the walk still owes. -/
private theorem twp_refill [WasmSmallStepGS hlc Universal.State]
    {hash : UInt32 → UInt64} {t : Table UInt32 UInt32}
    (hw : Table.Layout hash t) (ctrl : UInt32) (target : List Nat)
    {out frame items l6 l7 l8 l9 l10 l11 : UInt32} {m l12 : UInt64}
    {b : Nat} {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hb : b < numGroups t) (hmask : m &&& Table.REP80 = m)
    (htarget : walkRest t b m = target) (hne : target ≠ []) :
    iprop(
      Slices.ByteSlice 0 ctrl t.ctrl ∗
      (∀ (b' : Nat) (m' : UInt64) (l6' : UInt32),
        ⌜b' < numGroups t ∧ walkRest t b' m' = target ∧ m' ≠ 0 ∧
          m' &&& Table.REP80 = m'⌝ -∗
        Slices.ByteSlice 0 ctrl t.ctrl -∗
        WP (.running
            ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b')) frame items
                (ctrl + UInt32.ofNat (8 * (b' + 1))) m' l6' l7 l8 l9 l10
                l11 l12,
              rest, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b)) frame items
              (ctrl + UInt32.ofNat (8 * (b + 1))) m l6 l7 l8 l9 l10 l11
              l12,
            .block 0 0 maskBlock :: rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hctrl, Hexit⟩
  simp only [maskBlock, walkLocals, rep80]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_localGet twp_constI64]
  by_cases hm : m = 0
  · subst hm
    iapply Wasm.SmallStep.twp_neI64 (result := 0)
      (by rw [if_neg (by simp)])
    wasm_twp_pures [twp_brIfZero]
    iapply twp_advance hw ctrl target (b := b) (mAny := 0) htarget hne
    isplitl_exact Hctrl
    · iintro %b' %l6' %hb' Hctrl
      obtain ⟨hb'lt, hb'walk, hb'ne⟩ := hb'
      wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64]
      isimp only [full_of_and_xor]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      ihave Hgo := Hexit $$ %b'
        %(Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * b')))) %l6'
        %(⟨hb'lt, hb'walk, hb'ne,
            Table.swarMatchFull_and_REP80 _⟩ :
          b' < numGroups t ∧
            walkRest t b'
                (Table.swarMatchFull
                  (Table.groupWord (Table.groupAt t (8 * b')))) = target ∧
            Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * b'))) ≠ 0 ∧
            Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * b'))) &&&
              Table.REP80 =
              Table.swarMatchFull
                (Table.groupWord (Table.groupAt t (8 * b'))))
        Hctrl
      iexact Hgo
  · iapply Wasm.SmallStep.twp_neI64 (result := 1) (by rw [if_pos hm])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave Hgo := Hexit $$ %b %m %l6
      %(⟨hb, htarget, hm, hmask⟩ :
        b < numGroups t ∧ walkRest t b m = target ∧ m ≠ 0 ∧
          m &&& Table.REP80 = m)
      Hctrl
    iexact Hgo

/-! ## The entries the push loop has written -/

/-- The entries of the first `len` full buckets, in bucket order. -/
private def pushedAt (t : Table UInt32 UInt32) (len : Nat) :
    List (UInt32 × UInt32) :=
  ((Table.fullIndices t).take len).filterMap t.slotAt

private theorem pushed_length {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.Layout hash t) (len : Nat) :
    (pushedAt t len).length = min len (Table.fullIndices t).length := by
  unfold pushedAt
  rw [Table.length_filterMap_of_isSome _ _ (fun j hj =>
    (hw.full_iff j (Table.mem_fullIndices.1
        (List.mem_of_mem_take hj)).1).1
      (Table.mem_fullIndices.1 (List.mem_of_mem_take hj)).2),
    List.length_take]

private theorem pushed_zero (t : Table UInt32 UInt32) :
    pushedAt t 0 = [] := rfl

private theorem pushed_all {hash : UInt32 → UInt64}
    {t : Table UInt32 UInt32} (hw : Table.Layout hash t) :
    pushedAt t (Table.fullIndices t).length = Table.toList t := by
  unfold pushedAt
  rw [List.take_of_length_le (Nat.le_refl _)]
  exact Table.filterMap_fullIndices hw

private theorem pushed_succ (t : Table UInt32 UInt32) {len : Nat}
    (hlen : len < (Table.fullIndices t).length) {k v : UInt32}
    (hslot : t.slotAt (Table.fullIndices t)[len] = some (k, v)) :
    pushedAt t (len + 1) = pushedAt t len ++ [(k, v)] := by
  unfold pushedAt
  rw [List.take_add_one, List.getElem?_eq_getElem hlen,
    List.filterMap_append]
  simp only [Option.toList, List.filterMap_cons, hslot, List.filterMap_nil]

/-! ## The lowest flagged byte -/

private theorem ctz_shape {m : UInt64} (hmask : m &&& Table.REP80 = m)
    (hne : m ≠ 0) :
    ctz64 64 m / 8 < 8 ∧ ctz64 64 m = 8 * (ctz64 64 m / 8) + 7 := by
  have hlow := Table.lowestSetByte_eq_ctz hmask hne
  have hj8 : ctz64 64 m / 8 < 8 :=
    List.mem_range.mp (List.mem_of_find?_eq_some hlow)
  obtain ⟨hbit, hmin⟩ := Table.lowest_bit_of_lowestSetByte hmask hlow
  refine ⟨hj8, ?_⟩
  have hstep := Table.ctz64_eq 64 (Nat.le_refl 64) m
    (8 * (ctz64 64 m / 8) + 7) (by omega) hbit hmin
  omega

/-- The byte offset of the lowest flagged byte, as the compiled code
computes it: `i64.ctz`, wrapped to `i32`, masked with 120. -/
private theorem wrap_ctz_and_120 {m : UInt64}
    (hmask : m &&& Table.REP80 = m) (hne : m ≠ 0) :
    UInt32.ofNat ((UInt64.ofNat (ctz64 64 m)).toNat % 2 ^ 32) &&& 120
      = UInt32.ofNat (8 * (ctz64 64 m / 8)) := by
  have hkey : ∀ j : Nat, j < 8 →
      UInt32.ofNat (8 * j + 7) &&& 120 = UInt32.ofNat (8 * j) := by
    intro j hj
    interval_cases j <;> decide
  obtain ⟨hj8, hctz⟩ := ctz_shape hmask hne
  have hmid : UInt32.ofNat ((UInt64.ofNat (ctz64 64 m)).toNat % 2 ^ 32)
      = UInt32.ofNat (8 * (ctz64 64 m / 8) + 7) := by
    congr 1
    rw [UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (by omega : ctz64 64 m < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : ctz64 64 m < 2 ^ 32)]
    exact hctz
  rw [hmid]
  exact hkey _ hj8

/-! ## The addresses of one bucket and one buffer entry -/

private theorem slot_addr_step (ctrl : UInt32) (b j : Nat) :
    ctrl - UInt32.ofNat (64 * b) - UInt32.ofNat (8 * j)
      = ctrl - UInt32.ofNat (8 * (8 * b + j)) := by
  rw [sub_sub_ofNat, show 64 * b + 8 * j = 8 * (8 * b + j) by omega]

private theorem keyAddr (ctrl : UInt32) (i : Nat) :
    ctrl - UInt32.ofNat (8 * i) - 8 = Table.bucketAddr ctrl i := by
  rw [← shl3_ofNat, slotAddr_of_wasm]

private theorem valueAddr (ctrl : UInt32) (i : Nat) :
    ctrl - UInt32.ofNat (8 * i) - 4 = Table.bucketAddr ctrl i + 4 := by
  rw [← shl3_ofNat, slotValueAddr_of_wasm]

private theorem negOneAdd (x : UInt32) : 4294967295 + x = x - 1 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967295 : UInt32).toNat = 4294967295 from rfl,
    show (1 : UInt32).toNat = 1 from rfl] at *

/-- Copy of `Func9Proof.lean:61`, which is private there. -/
private theorem ofNat_ne_zero {n : Nat} (h1 : 1 ≤ n) (h2 : n < UInt32.size) :
    UInt32.ofNat n ≠ (0 : UInt32) := by
  intro hc
  have hnat := congrArg UInt32.toNat hc
  rw [UInt32.toNat_ofNat_of_lt' h2, UInt32.toNat_zero] at hnat
  omega

private theorem ofNat_sub_one {n : Nat} (h1 : 1 ≤ n)
    (h2 : n < UInt32.size) :
    UInt32.ofNat n - 1 = UInt32.ofNat (n - 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' h2,
    UInt32.toNat_ofNat_of_lt' (by omega : n - 1 < UInt32.size),
    show (1 : UInt32).toNat = 1 from rfl]
  simp only [UInt32.size] at *
  omega

private theorem one_add_ofNat {n : Nat} (h : n + 1 < UInt32.size) :
    1 + UInt32.ofNat n = UInt32.ofNat (n + 1) := by
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_add, UInt32.toNat_ofNat_of_lt' (by omega),
    UInt32.toNat_ofNat_of_lt' h, show (1 : UInt32).toNat = 1 from rfl]
  simp only [UInt32.size] at *
  omega

/-- Move an owned range between two names of one address.  Copy of
`Func98Proof.lean:29`. -/
private theorem sliceMove [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {bytes : List UInt8}
    (haddress : address = address') :
    Slices.ByteSlice 0 address bytes ⊢
      Slices.ByteSlice 0 address' bytes := by
  rw [haddress]

/-- Move an owned word between two names of one address. -/
private theorem wordMove32 [WasmSmallStepGS hlc Universal.State]
    {address address' : UInt32} {value : UInt32}
    (haddress : address = address') :
    pointsTo_u32 0 address value ⊢ pointsTo_u32 0 address' value := by
  rw [haddress]

/-! ## The push loop

WAT 1151 to 1246.  One turn reads one full bucket and writes one entry
into the buffer. -/

/-- The index of the push loop.  `len` counts the entries already written
and `b` and `m` hold the walk.  The other four fields are dead machine
registers that the body writes. -/
private structure PushIdx where
  len : Nat
  b : Nat
  m : UInt64
  l6 : UInt32
  l7 : UInt32
  l9 : UInt32
  l12 : UInt64

private theorem buf_next (ptr : UInt32) (len : Nat) :
    ptr + UInt32.ofNat (8 * len) + UInt32.ofNat 8
      = ptr + UInt32.ofNat (8 * (len + 1)) := by
  rw [UInt32.add_assoc, ← UInt32.ofNat_add,
    show 8 * len + 8 = 8 * (len + 1) by omega]

/-- The resources that one turn of the push loop keeps. -/
private def PushInv [WasmSmallStepGS hlc Universal.State]
    (t : Table UInt32 UInt32) (ctrl fbase ptr w0 capW : UInt32)
    (cap : Nat) (i : PushIdx) : HeapIProp :=
  iprop(
    ⌜i.len < (Table.fullIndices t).length ∧ 1 ≤ i.len ∧
      i.b < numGroups t ∧ i.m &&& Table.REP80 = i.m ∧
      walkRest t i.b i.m = (Table.fullIndices t).drop i.len⌝ ∗
    Slices.ByteSlice 0 ctrl t.ctrl ∗
    Table.slotsBefore 0 ctrl t.slots ∗
    arrayAt 0 fbase [w0, capW, ptr, UInt32.ofNat i.len] ∗
    Table.PairSlice 0 ptr (pushedAt t i.len) ∗
    (∃ spare : List UInt8,
      ⌜spare.length = 8 * cap - 8 * i.len⌝ ∗
      Slices.ByteSlice 0 (ptr + UInt32.ofNat (8 * i.len)) spare))

/-- What the caller of the push loop gets when the loop ends. -/
private def PushExit [WasmSmallStepGS hlc Universal.State]
    (t : Table UInt32 UInt32) (ctrl fbase out ptr w0 capW l10 : UInt32)
    (cap : Nat) (rest : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (st : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp) :
    HeapIProp :=
  iprop(∀ (b' : Nat) (m' : UInt64) (l6' l7' l9' : UInt32) (l12' : UInt64)
      (spare : List UInt8),
    ⌜spare.length = 8 * cap - 8 * (Table.fullIndices t).length⌝ -∗
    Slices.ByteSlice 0 ctrl t.ctrl -∗
    Table.slotsBefore 0 ctrl t.slots -∗
    arrayAt 0 fbase
      [w0, capW, ptr, UInt32.ofNat (Table.fullIndices t).length] -∗
    Table.PairSlice 0 ptr (Table.toList t) -∗
    Slices.ByteSlice 0
      (ptr + UInt32.ofNat (8 * (Table.fullIndices t).length)) spare -∗
    WP (.running
        ⟨walkLocals out (ctrl - UInt32.ofNat (64 * b')) fbase
            (UInt32.ofNat (Table.fullIndices t).length)
            (ctrl + UInt32.ofNat (8 * (b' + 1))) m' l6' l7' 0 l9' l10 ptr
            l12',
          rest, arity, remainder, controls, calls⟩ :
        Expr Universal.State) @ st; E [{ Φ }])

set_option maxHeartbeats 2000000 in
/-- The push loop writes one entry per turn, in ascending bucket order,
and leaves the buffer holding `Table.toList`. -/
private theorem twp_pushLoop [WasmSmallStepGS hlc Universal.State]
    {hash : UInt32 → UInt64} {t : Table UInt32 UInt32}
    (hw : Table.Layout hash t) (ctrl fbase out ptr w0 capW l10 : UInt32)
    (cap : Nat) (i0 : PushIdx)
    {rest : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {st : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hroom : 8 * t.buckets ≤ ctrl.toNat)
    (hcapW : capW = UInt32.ofNat cap)
    (hNcap : (Table.fullIndices t).length ≤ cap)
    (hcapLt : cap < UInt32.size)
    (hptr : ptr.toNat + 8 * cap < UInt32.size)
    (hfbase : fbase.toNat + 16 ≤ UInt32.size) :
    iprop(PushInv t ctrl fbase ptr w0 capW cap i0 ∗
        PushExit t ctrl fbase out ptr w0 capW l10 cap rest arity remainder
          controls calls st E Φ) ⊢
      WP (.running
          ⟨walkLocals out (ctrl - UInt32.ofNat (64 * i0.b)) fbase
              (UInt32.ofNat i0.len)
              (ctrl + UInt32.ofNat (8 * (i0.b + 1))) i0.m i0.l6 i0.l7
              (UInt32.ofNat ((Table.fullIndices t).length - i0.len)) i0.l9
              l10 ptr i0.l12,
            .loop 0 0 pushLoop :: rest, arity, remainder, controls,
            calls⟩ : Expr Universal.State) @ st; E [{ Φ }] := by
  iintro ⟨Hinv, Hexit⟩
  have hctrlLt : ctrl.toNat < UInt32.size := ctrl.toNat_lt
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := PushIdx)
    (measure := fun i => (Table.fullIndices t).length - i.len)
    (locals := fun i =>
      walkLocals out (ctrl - UInt32.ofNat (64 * i.b)) fbase
        (UInt32.ofNat i.len) (ctrl + UInt32.ofNat (8 * (i.b + 1))) i.m
        i.l6 i.l7 (UInt32.ofNat ((Table.fullIndices t).length - i.len))
        i.l9 l10 ptr i.l12)
    (I := fun i => iprop(PushInv t ctrl fbase ptr w0 capW cap i ∗
      PushExit t ctrl fbase out ptr w0 capW l10 cap rest arity remainder
        controls calls st E Φ))
    (initial := i0)
    (initialLocals :=
      walkLocals out (ctrl - UInt32.ofNat (64 * i0.b)) fbase
        (UInt32.ofNat i0.len) (ctrl + UInt32.ofNat (8 * (i0.b + 1))) i0.m
        i0.l6 i0.l7
        (UInt32.ofNat ((Table.fullIndices t).length - i0.len)) i0.l9 l10
        ptr i0.l12)
    rfl rfl
  · intro i
    iintro Hrec ⟨Hinv, Hexit⟩
    isimp only [PushInv] at Hinv
    icases Hinv with ⟨%hpure, Hctrl, Hslots, Hframe, Hbuf,
      ⟨%spare, %hspare, Hspare⟩⟩
    obtain ⟨hlenN, hlen1, hb, hmask, hwalk⟩ := hpure
    simp only [Wasm.SmallStep.loopBodyExpr, pushLoop]
    iapply twp_refill hw ctrl ((Table.fullIndices t).drop i.len) hb hmask
      hwalk (by
        intro hc
        rw [List.drop_eq_nil_iff] at hc
        omega)
    isplitl_exact Hctrl
    · iintro %b' %m' %l6' %hpost Hctrl
      obtain ⟨hb', hwalk', hm'ne, hm'mask⟩ := hpost
      have hpop := walkRest_pop t hm'mask hm'ne (b := b')
      have hdrop : (Table.fullIndices t).drop i.len
          = (Table.fullIndices t)[i.len] ::
            (Table.fullIndices t).drop (i.len + 1) :=
        List.drop_eq_getElem_cons hlenN
      obtain ⟨hidx, hrest⟩ :=
        List.cons.inj (hdrop.symm.trans (hwalk'.symm.trans hpop))
      have hidxMem : (Table.fullIndices t)[i.len] ∈ Table.fullIndices t :=
        List.getElem_mem hlenN
      obtain ⟨hidxLt, hidxFull⟩ := Table.mem_fullIndices.1 hidxMem
      obtain ⟨k, v, hslot⟩ : ∃ k v,
          t.slotAt (Table.fullIndices t)[i.len] = some (k, v) := by
        have hsome := (hw.full_iff _ hidxLt).1 hidxFull
        cases hc : t.slotAt (Table.fullIndices t)[i.len] with
        | none => rw [hc] at hsome; exact absurd hsome (by decide)
        | some kv => exact ⟨kv.1, kv.2, rfl⟩
      have hIlen : (Table.fullIndices t)[i.len] < t.slots.length := by
        rw [hw.slots_len]; exact hidxLt
      have hslotsGet : t.slots[(Table.fullIndices t)[i.len]]'hIlen
          = some (k, v) := by
        rw [← hslot, Table.slotAt, List.getD_eq_getElem]
      have hbaddr := Table.bucketAddr_toNat ctrl hidxLt hroom
      have hbucketLt :
          8 * ((Table.fullIndices t)[i.len] + 1) ≤ ctrl.toNat := by
        have : (Table.fullIndices t)[i.len] + 1 ≤ t.buckets := by omega
        omega
      obtain ⟨ha1, ha2, ha3⟩ := addr3
        (Table.bucketAddr ctrl (Table.fullIndices t)[i.len]) (by omega)
      have hv0 :
          (Table.bucketAddr ctrl (Table.fullIndices t)[i.len] + 4).toNat
            = (Table.bucketAddr ctrl (Table.fullIndices t)[i.len]).toNat
              + 4 := by
        simpa using Slices.byteOffset_toNat
          (Table.bucketAddr ctrl (Table.fullIndices t)[i.len]) 4 (by omega)
      obtain ⟨hv1, hv2, hv3⟩ := addr3
        (Table.bucketAddr ctrl (Table.fullIndices t)[i.len] + 4) (by omega)
      ihave ⟨Hpre, Hcell, Hpost⟩ :=
        (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mp $$ Hslots
      isimp only [hslotsGet, Table.slotCell] at Hcell
      ihave ⟨Hkey, Hval⟩ := Hcell
      simp only [walkLocals]
      wasm_twp_pures [twp_localGet twp_constI64 twp_addI64]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_localGet twp_ctzI64 twp_wrapI64
        twp_const twp_and twp_sub]
      isimp only [wrap_ctz_and_120 hm'mask hm'ne, slot_addr_step, ← hidx]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_const twp_add]
      isimp only [negFourAdd, valueAddr]
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr v hv1 hv2 hv3
        with Hval
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [negEightAdd, keyAddr]
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr k ha1 ha2 ha3
        with Hkey
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      ihave Hslots : Table.slotsBefore 0 ctrl t.slots $$
        [Hpre Hkey Hval Hpost]
      · iapply (Table.slotsBefore_focus 0 ctrl t.slots hIlen).mpr
        isimp only [hslotsGet, Table.slotCell]
        iframe Hpre Hkey Hval Hpost
      -- the dead grow arm, WAT 1203 to 1218
      have hlencap : UInt32.ofNat i.len ≠ capW := by
        rw [hcapW]
        intro hc
        have hnat := congrArg UInt32.toNat hc
        rw [UInt32.toNat_ofNat_of_lt' (by omega),
          UInt32.toNat_ofNat_of_lt' hcapLt] at hnat
        omega
      have hf4 := offset_facts fbase 4 4 rfl (by omega)
      have hf12 := offset_facts fbase 12 12 rfl (by omega)
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      wasm_twp_pures [twp_localGet twp_localGet]
      ihave ⟨Hcell1, Hback1⟩ := cell_load fbase 4
        [w0, capW, ptr, UInt32.ofNat i.len] 1 capW (by simp) rfl rfl
        $$ Hframe
      wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := fbase)
        (offset := 4) capW hf4.1 hf4.2.1 hf4.2.2.1 hf4.2.2.2 with Hcell1
      ihave Hframe := Hback1 $$ Hcell1
      iapply Wasm.SmallStep.twp_ne (result := 1) (by rw [if_pos hlencap])
      iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
      simp only [List.take_zero, List.nil_append]
      -- the iterator step
      wasm_twp_pures [twp_localGet twp_localGet twp_andI64_bits]
      isimp only [UInt64.and_comm (m' + 18446744073709551615) m']
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      -- the entry write
      have haddrNat : (ptr + UInt32.ofNat (8 * i.len)).toNat
          = ptr.toNat + 8 * i.len :=
        Slices.byteOffset_toNat ptr (8 * i.len) (by omega)
      have hnowrap8 :
          (ptr + UInt32.ofNat (8 * i.len)).toNat + 8 < UInt32.size := by
        rw [haddrNat]; omega
      have hspare8 : 8 ≤ spare.length := by omega
      have htake8 : (spare.take 8).length = 8 := by
        rw [List.length_take, Nat.min_eq_left hspare8]
      have happ := (Slices.ByteSlice_append (α := Universal.State) 0
        (ptr + UInt32.ofNat (8 * i.len)) (spare.take 8) (spare.drop 8)).mp
      rw [List.take_append_drop, htake8] at happ
      ihave ⟨Hhead, Htail⟩ := happ $$ Hspare
      ihave ⟨%sw0, %sw1, Hw0, Hw1⟩ := outWords 0
        (ptr + UInt32.ofNat (8 * i.len)) (spare.take 8) htake8 hnowrap8
        $$ Hhead
      have hst4 := offset_facts (ptr + UInt32.ofNat (8 * i.len)) 4 4 rfl
        (by omega)
      have hst0 := offset_facts (ptr + UInt32.ofNat (8 * i.len)) 0 0 rfl
        (by omega)
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
      isimp only [shl32Wasm3, shl3_ofNat,
        UInt32.add_comm (UInt32.ofNat (8 * i.len)) ptr]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind Wasm.SmallStep.twp_store32
        (address := ptr + UInt32.ofNat (8 * i.len)) (offset := 4) sw1
        hst4.1 hst4.2.1 hst4.2.2.1 hst4.2.2.2 with Hw1
      wasm_twp_pures [twp_localGet twp_localGet]
      ihave Hw0 := wordMove32 (UInt32.add_zero _).symm $$ Hw0
      wasm_twp_rebind Wasm.SmallStep.twp_store32
        (address := ptr + UInt32.ofNat (8 * i.len)) (offset := 0) sw0
        hst0.1 hst0.2.1 hst0.2.2.1 hst0.2.2.2 with Hw0
      ihave Hw0 := wordMove32 (UInt32.add_zero _) $$ Hw0
      have hplen : (pushedAt t i.len).length = i.len := by
        rw [pushed_length hw]; omega
      ihave Hbuf : Table.PairSlice 0 ptr (pushedAt t (i.len + 1)) $$
        [Hbuf Hw0 Hw1]
      · rw [pushed_succ t hlenN hslot]
        iapply (Table.PairSlice_split 0 ptr
          (pushedAt t i.len ++ [(k, v)]) i.len
          (by rw [List.length_append, hplen]; omega)).mpr
        rw [List.take_left' hplen, List.drop_left' hplen]
        isplitl_exact Hbuf
        · isimp only [Table.PairSlice, Table.pairBytes_single]
          iapply (Table.ByteSlice_pair_as_words 0
            (ptr + UInt32.ofNat (8 * i.len)) (k, v)).mpr
          isplitl_pureexact hnowrap8
          · iframe Hw0 Hw1
      ihave Htail := sliceMove (buf_next ptr i.len) $$ Htail
      -- the length word
      wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
      isimp only [one_add_ofNat (show i.len + 1 < UInt32.size by omega)]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      ihave ⟨Hcell3, Hback3⟩ := cell_focus fbase 12
        [w0, capW, ptr, UInt32.ofNat i.len] 3 (UInt32.ofNat i.len)
        (UInt32.ofNat (i.len + 1)) (by simp) rfl rfl $$ Hframe
      wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := fbase)
        (offset := 12) (UInt32.ofNat i.len) hf12.1 hf12.2.1 hf12.2.2.1
        hf12.2.2.2 with Hcell3
      ihave Hframe := Hback3 $$ Hcell3
      isimp only [List.set] at Hframe
      -- the counter
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [negOneAdd,
        ofNat_sub_one (show 1 ≤ (Table.fullIndices t).length - i.len by
          omega) (show (Table.fullIndices t).length - i.len < UInt32.size by
          omega)]
      isimp only [Nat.sub_sub]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      by_cases hdone : i.len + 1 = (Table.fullIndices t).length
      · -- the last turn: the loop falls through
        isimp only [hdone, Nat.sub_self,
          show UInt32.ofNat 0 = (0 : UInt32) from rfl]
        wasm_twp_pures [twp_brIfZero twp_exitControl]
        simp only [List.take_zero, List.nil_append]
        isimp only [hdone] at Hframe
        isimp only [hdone] at Hbuf
        isimp only [pushed_all hw] at Hbuf
        isimp only [hdone] at Htail
        isimp only [PushExit] at Hexit
        ihave Hgo := Hexit $$ %b' %(m' &&& (m' + 18446744073709551615))
          %k %v %(ptr + UInt32.ofNat (8 * i.len))
          %(m' + 18446744073709551615) %(spare.drop 8)
          %(show (spare.drop 8).length
              = 8 * cap - 8 * (Table.fullIndices t).length by
            rw [List.length_drop]; omega)
          Hctrl Hslots Hframe Hbuf Htail
        iexact Hgo
      · -- one more turn
        have hne0 :
            UInt32.ofNat ((Table.fullIndices t).length - (i.len + 1))
              ≠ 0 := ofNat_ne_zero (by omega) (by omega)
        iapply Wasm.SmallStep.twp_brIf hne0 (by rfl)
        simp only [List.take_zero, List.nil_append]
        ihave Hback := Hrec
          $$ %(⟨i.len + 1, b', m' &&& (m' + 18446744073709551615), k, v,
              ptr + UInt32.ofNat (8 * i.len),
              m' + 18446744073709551615⟩ : PushIdx)
            %(by simp only []; omega)
        iapply Hback
        isplitl [Hctrl Hslots Hframe Hbuf Htail]
        · isimp only [PushInv]
          isplitl_pureexact
            (⟨by omega, by omega, hb', iterNext_and_REP80 hm'mask,
              hrest.symm⟩ :
              i.len + 1 < (Table.fullIndices t).length ∧
                1 ≤ i.len + 1 ∧ b' < numGroups t ∧
                (m' &&& (m' + 18446744073709551615)) &&& Table.REP80
                  = m' &&& (m' + 18446744073709551615) ∧
                walkRest t b' (m' &&& (m' + 18446744073709551615))
                  = (Table.fullIndices t).drop (i.len + 1))
          · isplitl_exact Hctrl
            · isplitl_exact Hslots
              · isplitl_exact Hframe
                · isplitl_exact Hbuf
                  · iexists (spare.drop 8)
                    isplitl_pureexact
                      (show (spare.drop 8).length
                          = 8 * cap - 8 * (i.len + 1) by
                        rw [List.length_drop]; omega)
                    · iexact Htail
        · iexact Hexit
  · iframe Hinv Hexit

/-! ## The item count and the two physical forms of a table -/

/-- The item count word of a table value, in either physical form.  The
static singleton reports zero, and its model has no item. -/
private theorem tableAt_items [WasmHeapGS Universal.State]
    (base : UInt32) (t : Table UInt32 UInt32) :
    Table.TableAt (α := Universal.State) 0 base t ⊢
      iprop(pointsTo_u32 0 (base + 12) (UInt32.ofNat t.items) ∗
        (pointsTo_u32 0 (base + 12) (UInt32.ofNat t.items) -∗
          Table.TableAt 0 base t)) := by
  iintro Htable
  isimp only [Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Harm⟩
  icases Harm with (Hsing | ⟨%hbuckets, Hbody⟩)
  · isimp only [Table.SingletonBody, Table.tableHeader] at Hsing
    icases Hsing with ⟨%hsing, ⟨H0, H4, H8, H12⟩, Hctrl⟩
    have hz : UInt32.ofNat t.items = (0 : UInt32) := by rw [hsing.2.1]; rfl
    ihave H12 : pointsTo_u32 0 (base + 12) (UInt32.ofNat t.items) $$ [H12]
    · rw [hz]
      iexact H12
    isplitl_exact H12
    · iintro H12
      ihave H12 : pointsTo_u32 0 (base + 12) (0 : UInt32) $$ [H12]
      · rw [← hz]
        iexact H12
      isimp only [Table.TableAt]
      iexists ctrl
      ileft
      isimp only [Table.SingletonBody, Table.tableHeader]
      isplitl_pureexact hsing
      · iframe H0 H4 H8 H12 Hctrl
  · isimp only [Table.TableBody, Table.tableHeader] at Hbody
    icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
    isplitl_exact H12
    · iintro H12
      isimp only [Table.TableAt]
      iexists ctrl
      iright
      isplitl_pureexact hbuckets
      · isimp only [Table.TableBody, Table.tableHeader]
        isplitl_pureexact hctrlBound
        · iframe H0 H4 H8 H12 Hctrl Hslots

/-- A table with an item is allocated: the static singleton has none. -/
private theorem tableAt_body [WasmHeapGS Universal.State]
    (base : UInt32) (t : Table UInt32 UInt32) (hitems : t.items ≠ 0) :
    Table.TableAt (α := Universal.State) 0 base t ⊢
      iprop(∃ ctrl : UInt32,
        ⌜1 < t.buckets⌝ ∗ Table.TableBody 0 base ctrl t) := by
  iintro Htable
  isimp only [Table.TableAt] at Htable
  icases Htable with ⟨%ctrl, Harm⟩
  icases Harm with (Hsing | ⟨%hbuckets, Hbody⟩)
  · isimp only [Table.SingletonBody] at Hsing
    icases Hsing with ⟨%hsing, H, Hctrl⟩
    exact absurd hsing.2.1 hitems
  · iexists ctrl
    isplitl_pureexact hbuckets
    · iexact Hbody

/-! ## The stack region

The body commits a 16-byte frame at the top of the region and hands the
rest to the sort.  The two lemmas below are copies of
`DriverTail.lean:56` and `DriverTail.lean:81`. -/

private theorem below_split [WasmHeapGS Universal.State]
    (sp : UInt32) (deep shallow : Nat) (bytes : List UInt8)
    (hle : shallow ≤ deep)
    (haddr : sp - UInt32.ofNat deep + UInt32.ofNat (deep - shallow)
      = sp - UInt32.ofNat shallow) :
    StackBelow sp deep bytes ⊢
      iprop(Slices.ByteSlice 0 (sp - UInt32.ofNat deep)
          (bytes.take (deep - shallow)) ∗
        StackBelow sp shallow (bytes.drop (deep - shallow))) := by
  iintro Hbelow
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  have hsplit : bytes.take (deep - shallow) ++ bytes.drop (deep - shallow)
      = bytes := List.take_append_drop _ _
  have htakeLength :
      (bytes.take (deep - shallow)).length = deep - shallow := by
    rw [List.length_take, hlength]; omega
  ihave ⟨Hlow, Hhigh⟩ :=
    (Slices.ByteSlice_append 0 (sp - UInt32.ofNat deep)
      (bytes.take (deep - shallow))
      (bytes.drop (deep - shallow))).mp $$ [Hbytes]
  · irw_exact [hsplit] with Hbytes
  isplitl_exact Hlow
  · isplitl_pureexact (by rw [List.length_drop, hlength]; omega)
    · irw_exact [htakeLength, haddr] with Hhigh

private theorem below_join [WasmHeapGS Universal.State]
    (sp : UInt32) (deep shallow : Nat) (low below : List UInt8)
    (hlow : low.length = deep - shallow) (hle : shallow ≤ deep)
    (haddr : sp - UInt32.ofNat deep + UInt32.ofNat (deep - shallow)
      = sp - UInt32.ofNat shallow) :
    iprop(Slices.ByteSlice 0 (sp - UInt32.ofNat deep) low ∗
        StackBelow sp shallow below) ⊢
      StackBelow sp deep (low ++ below) := by
  iintro ⟨Hlow, Hbelow⟩
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  isplitl_pureexact (by rw [List.length_append, hlow, hlength]; omega)
  · iapply (Slices.ByteSlice_append 0 (sp - UInt32.ofNat deep) low
      below).mpr
    isplitl_exact Hlow
    · irw_exact [hlow, haddr] with Hbytes

/-- The address of the frame after the deep reserve.  The frame is the
top 16 bytes of the region that the body owns. -/
private theorem stack_split_addr (sp : UInt32) (deep : Nat)
    (hle : 16 ≤ deep) :
    sp - UInt32.ofNat deep + UInt32.ofNat (deep - 16)
      = sp - UInt32.ofNat 16 := by
  obtain ⟨e, rfl⟩ : ∃ e, deep = 16 + e := ⟨deep - 16, by omega⟩
  rw [Nat.add_sub_cancel_left, UInt32.ofNat_add,
    ← Table.sub_sub_addr, UInt32.sub_add_cancel]

/-- A list of one entry or none is in key order. -/
private theorem sorted_of_length_le_one {l : List (UInt32 × UInt32)}
    (h : l.length ≤ 1) : Table.SortedByKey l := by
  match l with
  | [] => simp [Table.SortedByKey]
  | [_] => simp [Table.SortedByKey]
  | _ :: _ :: _ => simp at h

/-- Rebuild the pair vector from the buffer and the spare bytes after
it. -/
private theorem pairVec_of_slice [WasmSmallStepGS hlc Universal.State]
    (heapId : GName) (allocationId cap : Nat) (ptr : UInt32)
    (pairs : List (UInt32 × UInt32)) (spare : List UInt8)
    (hcap : cap ≠ 0)
    (hspare : spare.length = 8 * cap - 8 * pairs.length)
    (hfit : pairs.length ≤ cap)
    (hptr : ptr ≠ 0) (halign : ptr.toNat % 4 = 0) :
    iprop(AllocToken heapId allocationId ptr (pairBlock cap) ∗
        Table.PairSlice 0 ptr pairs ∗
        Slices.ByteSlice 0 (ptr + UInt32.ofNat (8 * pairs.length))
          spare) ⊢
      PairVecAt heapId allocationId cap ptr pairs := by
  iintro ⟨Htoken, Hbuf, Hspare⟩
  isimp only [PairVecAt, if_neg hcap]
  iexists spare
  isplitl_pureexact (by
    rw [List.length_append, Table.pairBytes_length, hspare]; omega)
  · isimp only [LiveBlock]
    isplitl_exact Htoken
    · isplitl [Hbuf Hspare]
      · isimp only [Table.PairSlice] at Hbuf
        iapply (Slices.ByteSlice_append 0 ptr (Table.pairBytes pairs)
          spare).mpr
        isplitl_exact Hbuf
        · irw_exact [Table.pairBytes_length] with Hspare
      · ipureexact ⟨by
          rw [List.length_append, Table.pairBytes_length, hspare]
          simp only [pairBlock]
          omega, hptr, by simpa only [pairBlock] using halign⟩

/-- The epilogue and the normal arm of the continuation.  The three exits
of the sort dispatch all reach it.  WAT 1295 to 1298. -/
private def TailExit [WasmSmallStepGS hlc Universal.State]
    (t : Table UInt32 UInt32) (sp out ctrl base capW : UInt32)
    (heapId : GName) (allocationId : Nat)
    (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (input output : List UInt8)
    (raised : Bool) (cframes : List CallFrame)
    (st : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(∀ (l1 l3 l4 l6 l7 l8 l9 l10 l11 w0 w1 w2 w3 : UInt32)
      (m l12 : UInt64) (pairs : List (UInt32 × UInt32))
      (below' : List UInt8),
    ⌜pairs.Perm (Table.toList t) ∧ Table.SortedByKey pairs⌝ -∗
    RuntimeContext -∗
    StackPointer (sp - 16) -∗
    StackBelow (sp - 16) (sortDepth t.items) below' -∗
    arrayAt 0 (sp - 16) [w0, w1, w2, w3] -∗
    Slices.ByteSlice 0 out
      (WordCodec.u32le.serialize [capW, base, UInt32.ofNat t.items]) -∗
    Slices.ByteSlice 0 ctrl t.ctrl -∗
    Table.slotsBefore 0 ctrl t.slots -∗
    BumpHeap heapId storedCursor frontier history -∗
    PairVecAt heapId allocationId capW.toNat base pairs -∗
    Streams input output raised -∗
    WP (.running ⟨walkLocals out l1 (sp - 16) l3 l4 m l6 l7 l8 l9 l10 l11
          l12, epilogue, 0, [], [], cframes⟩ :
        Expr Universal.State) @ st; E [{ Φ }])

/-! ## The proof of the contract -/

set_option maxRecDepth 1048576 in
set_option maxHeartbeats 2000000 in
/-- `sorted_entries` walks the table, copies every entry into a fresh
buffer and sorts that buffer by key. -/
theorem func4_correct [WasmSmallStepGS hlc Universal.State] :
    Func4Spec (hlc := hlc) := by
  unfold Func4Spec CallContract callExpr
  intro sp out map k0 k1 t outBefore below heapId storedCursor frontier
    history input output raised callerLocals stack code arity remainder
    controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hbump, Hstreams, %hpure,
    Hcont⟩
  obtain ⟨houtLen, hwf, hbuckets27, houtBound, hmapBound, hdepth⟩ := hpure
  have hsize : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < UInt32.size := sp.toNat_lt
  have hdeep : 16 ≤ sortedEntriesDepth t.items := by
    unfold sortedEntriesDepth
    omega
  have hspLow : 16 ≤ sp.toNat := by omega
  have hfbNat : (sp - 16).toNat = sp.toNat - 16 := by
    have hx := UInt32.toNat_lt sp
    simp only [UInt32.toNat_sub,
      show (16 : UInt32).toNat = 16 from rfl, UInt32.size] at *
    omega
  have hh12 := offset_facts map 12 12 rfl (by omega)
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 7
      Project.RustHashMap.func4Def (by decide) func4_index with Hmodule
  simp only [Project.RustHashMap.func4Def, Function.toLocals,
    Function.numParams, List.length_cons, List.length_nil, List.take,
    List.drop, List.reverse_cons, List.reverse_nil, List.map,
    List.nil_append, List.cons_append, ValueType.zero, func4_shape,
    Nat.reduceAdd]
  iclose_map_runtime Hruntime with Hmodule Henv
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_block]
  simp only [List.drop_zero]
  wasm_twp_pures [twp_localGet]
  isimp only [Table.HashMapAt] at Hmap
  icases Hmap with ⟨Htable, Hk0, Hk1⟩
  ihave ⟨Hitems, Hclose⟩ := tableAt_items map t $$ Htable
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := map) (offset := 12)
    (UInt32.ofNat t.items) hh12.1 hh12.2.1 hh12.2.2.1 hh12.2.2.2
    with Hitems
  ihave Htable := Hclose $$ Hitems
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  have hitemsLe : t.items ≤ t.buckets := by
    rw [hwf.items_eq]
    exact Table.length_toList_le hwf.toLayout
  have hitemsLt : t.items < UInt32.size := by omega
  have hspBack : (16 : UInt32) + (sp - 16) = sp := by
    rw [UInt32.add_comm, UInt32.sub_add_cancel]
  have hout4 : out + 4 + 4 = out + 8 := by
    rw [UInt32.add_assoc]
    rfl
  have hout0 : out + 0 = out := UInt32.add_zero out
  have ho8 := offset_facts out 8 8 rfl (by omega)
  have ho0 := offset_facts64 out 0 0 rfl (by omega)
  by_cases hitems : t.items = 0
  · -- the empty table, WAT 1288 to 1293
    have hzero : UInt32.ofNat t.items = (0 : UInt32) := by rw [hitems]; rfl
    have hlist : Table.toList t = [] := by
      have hlen := hwf.items_eq
      rw [hitems] at hlen
      exact List.eq_nil_of_length_eq_zero hlen.symm
    iapply Wasm.SmallStep.twp_eqz (result := 1) (by rw [if_pos hzero])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave ⟨%houtWords, Houtcells⟩ :=
      ByteSlice_as_cells out outBefore 3 (by omega) $$ Hout
    obtain ⟨o0, o1, o2, houtShape⟩ := three_words _ houtWords
    isimp only [houtShape, arrayAt] at Houtcells
    icases Houtcells with ⟨Ho0, Ho1, Ho2, Hemp⟩
    wasm_twp_pures [twp_localGet twp_const]
    ihave Ho2 := wordMove32 hout4 $$ Ho2
    wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out)
      (offset := 8) o2 ho8.1 ho8.2.1 ho8.2.2.1 ho8.2.2.2 with Ho2
    wasm_twp_pures [twp_localGet twp_constI64]
    ihave Hpair := (pointsTo_u32_pair_as_groupWord 0 out o0 o1).mp $$
      [Ho0 Ho1]
    · isplitl_exact Ho0
      · iexact Ho1
    ihave Hpair := wordMove64 hout0.symm $$ Hpair
    wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out)
      (offset := 0) (wordPair o0 o1) ho0.1 ho0.2.1 ho0.2.2.1 ho0.2.2.2.1
      ho0.2.2.2.2.1 ho0.2.2.2.2.2.1 ho0.2.2.2.2.2.2.1 ho0.2.2.2.2.2.2.2
      with Hpair
    ihave Hpair := wordMove64 hout0 $$ Hpair
    ihave ⟨Ho0, Ho1⟩ : iprop(pointsTo_u32 0 out 0 ∗
        pointsTo_u32 0 (out + 4) 4) $$ [Hpair]
    · iapply (pointsTo_u32_pair_as_groupWord 0 out 0 4).mpr
      irw_exact [show wordPair 0 4 = (17179869184 : UInt64) from rfl]
        with Hpair
    ihave Ho2 := wordMove32 hout4.symm $$ Ho2
    ihave Houtcells : arrayAt 0 out [0, 4, UInt32.ofNat t.items] $$
      [Ho0 Ho1 Ho2 Hemp]
    · isimp only [arrayAt, hzero]
      isplitl_exact Ho0
      · isplitl_exact Ho1
        · isplitl_exact Ho2
          · iexact Hemp
    ihave Hout := ByteSlice_of_cells out [0, 4, UInt32.ofNat t.items]
      (by simp only [List.length_cons, List.length_nil]; omega) $$
      Houtcells
    wasm_twp_pures [twp_exitControl]
    simp only [List.take_zero, List.nil_append]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [hspBack]
    wasm_twp_rebind twp_globalSet with Hsp
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough
      with Hmodule
    simp only [List.take_zero, List.nil_append]
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hsp : StackPointer sp $$ [Hsp]
    · isimp only [StackPointer]
      iexact Hsp
    ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$ [Htable Hk0 Hk1]
    · isimp only [Table.HashMapAt]
      isplitl_exact Htable
      · isplitl_exact Hk0
        · iexact Hk1
    ihave Hpv : PairVecAt heapId 0 (UInt32.toNat (0 : UInt32)) 4
        (sortByKey (Table.toList t)) $$ []
    · isimp only [PairVecAt,
        if_pos (show UInt32.toNat (0 : UInt32) = 0 from rfl)]
      ipureexact
        (⟨trivial, by rw [hlist]; simp [sortByKey]⟩ :
          True ∧ sortByKey (Table.toList t) = [])
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %(0 : UInt32) %(4 : UInt32) %(0 : Nat)
      %below %storedCursor %frontier %history
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
    iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hmap Hbump Hpv Hstreams
      %(show UInt32.toNat (0 : UInt32)
          = if t.items = 0 then 0 else max t.items 4 by
        rw [if_pos hitems]
        rfl)
  · -- the table has an entry, WAT 1036 to 1286
    have hitemsPos : 1 ≤ t.items := by omega
    have hNitems : (Table.fullIndices t).length = t.items := by
      rw [Table.length_fullIndices hwf.toLayout, hwf.items_eq]
    have hNpos : (Table.fullIndices t).length ≠ 0 := by omega
    have hcapLt : max t.items 4 < UInt32.size := by
      simp only [UInt32.size] at *
      omega
    have hsel : Value.i32 (UInt32.ofNat (max t.items 4))
        = if (if (4 : UInt32) < UInt32.ofNat t.items then (1 : UInt32)
              else 0) ≠ 0
          then Value.i32 (UInt32.ofNat t.items)
          else Value.i32 (UInt32.ofNat 4) := by
      have hfour : (4 : UInt32).toNat = 4 := rfl
      by_cases hbig : (4 : UInt32) < UInt32.ofNat t.items
      · rw [if_pos hbig, if_pos (by decide : (1 : UInt32) ≠ 0)]
        rw [UInt32.lt_iff_toNat_lt, hfour,
          UInt32.toNat_ofNat_of_lt' hitemsLt] at hbig
        rw [Nat.max_eq_left (by omega)]
      · rw [if_neg hbig, if_neg (by decide : ¬((0 : UInt32) ≠ 0))]
        rw [UInt32.lt_iff_toNat_lt, hfour,
          UInt32.toNat_ofNat_of_lt' hitemsLt, Nat.not_lt] at hbig
        rw [Nat.max_eq_right hbig]
    ihave ⟨%ctrl, %hbuckets1, Hbody⟩ := tableAt_body map t hitems $$ Htable
    isimp only [Table.TableBody, Table.tableHeader] at Hbody
    icases Hbody with ⟨%hctrlBound, ⟨H0, H4, H8, H12⟩, Hctrl, Hslots⟩
    have hctrlLt : ctrl.toNat < UInt32.size := ctrl.toNat_lt
    obtain ⟨hm1, hm2, hm3⟩ := addr3 map (by omega)
    iapply Wasm.SmallStep.twp_eqz (result := 0)
      (by rw [if_neg (ofNat_ne_zero hitemsPos hitemsLt)])
    wasm_twp_pures [twp_brIfZero twp_localGet]
    wasm_twp_rebind Wasm.SmallStep.twp_load32_addr ctrl hm1 hm2 hm3 with H0
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_const twp_add]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply twp_peel hwf.toLayout ctrl (Table.fullIndices t)
      (walkRest_start hwf.toLayout)
      (by
        intro hc
        rw [hc] at hNitems
        simp only [List.length_nil] at hNitems
        omega)
    isplitl_exact Hctrl
    · iintro %b0 %l60 %hb0 Hctrl
      obtain ⟨hb0lt, hb0walk, hb0ne⟩ := hb0
      simp only [walkLocals, capTail]
      wasm_twp_pures [twp_localGet twp_const twp_localGet twp_const
        twp_gtU]
      iapply Wasm.SmallStep.twp_select hsel
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_const twp_shl]
      isimp only [shl32Wasm3, shl3_ofNat]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_const]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_block]
      simp only [List.drop_zero]
      -- the two dead capacity guards, WAT 1084 to 1091
      have h27 : (2 : Nat) ^ 27 = 134217728 := by norm_num
      have hg1 : ¬ (UInt32.ofNat t.items > (536870911 : UInt32)) := by
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hitemsLt,
          show (536870911 : UInt32).toNat = 536870911 from rfl, Nat.not_lt]
        omega
      have hmulLt : 8 * max t.items 4 < UInt32.size := by
        simp only [UInt32.size]
        omega
      have hg2 : ¬ (UInt32.ofNat (8 * max t.items 4)
          > (2147483644 : UInt32)) := by
        rw [gt_iff_lt, UInt32.lt_iff_toNat_lt,
          UInt32.toNat_ofNat_of_lt' hmulLt,
          show (2147483644 : UInt32).toNat = 2147483644 from rfl,
          Nat.not_lt]
        omega
      wasm_twp_pures [twp_localGet twp_const]
      iapply Wasm.SmallStep.twp_gtU (result := 0) (by rw [if_neg hg1])
      wasm_twp_pures [twp_brIfZero twp_localGet twp_const]
      iapply Wasm.SmallStep.twp_gtU (result := 0) (by rw [if_neg hg2])
      wasm_twp_pures [twp_brIfZero]
      -- the first entry, WAT 1092 to 1111
      have hm0mask := Table.swarMatchFull_and_REP80
        (Table.groupWord (Table.groupAt t (8 * b0)))
      have hpop0 := walkRest_pop t hm0mask hb0ne (b := b0)
      have hfi : Table.fullIndices t
          = (8 * b0 +
              ctz64 64
                (Table.swarMatchFull
                  (Table.groupWord (Table.groupAt t (8 * b0)))) / 8) ::
            walkRest t b0
              (Table.swarMatchFull
                  (Table.groupWord (Table.groupAt t (8 * b0))) &&&
                (Table.swarMatchFull
                    (Table.groupWord (Table.groupAt t (8 * b0))) +
                  18446744073709551615)) := hb0walk.symm.trans hpop0
      have hidx0Mem : (8 * b0 +
          ctz64 64 (Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)
          ∈ Table.fullIndices t := by
        rw [hfi]
        exact List.mem_cons_self
      obtain ⟨hidx0Lt, hidx0Full⟩ := Table.mem_fullIndices.1 hidx0Mem
      obtain ⟨key0, val0, hslot0⟩ : ∃ a b,
          t.slotAt (8 * b0 +
            ctz64 64 (Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)
            = some (a, b) := by
        have hsome := (hwf.toLayout.full_iff _ hidx0Lt).1 hidx0Full
        cases hc : t.slotAt (8 * b0 +
            ctz64 64 (Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b0)))) / 8) with
        | none => rw [hc] at hsome; exact absurd hsome (by decide)
        | some kv => exact ⟨kv.1, kv.2, rfl⟩
      have hIlen0 : (8 * b0 +
          ctz64 64 (Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)
          < t.slots.length := by
        rw [hwf.toLayout.slots_len]; exact hidx0Lt
      have hslotsGet0 : t.slots[(8 * b0 +
          ctz64 64 (Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)]'hIlen0
          = some (key0, val0) := by
        rw [← hslot0, Table.slotAt, List.getD_eq_getElem]
      have hbaddr0 := Table.bucketAddr_toNat ctrl hidx0Lt hctrlBound
      obtain ⟨hk1, hk2, hk3⟩ := addr3
        (Table.bucketAddr ctrl (8 * b0 +
          ctz64 64 (Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)) (by omega)
      have hvz : (Table.bucketAddr ctrl (8 * b0 +
            ctz64 64 (Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)
          + 4).toNat
          = (Table.bucketAddr ctrl (8 * b0 +
            ctz64 64 (Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)).toNat
            + 4 := by
        simpa using Slices.byteOffset_toNat _ 4 (by omega)
      obtain ⟨hvv1, hvv2, hvv3⟩ := addr3
        (Table.bucketAddr ctrl (8 * b0 +
          ctz64 64 (Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * b0)))) / 8) + 4)
        (by omega)
      ihave ⟨Hpre0, Hcell0, Hpost0⟩ :=
        (Table.slotsBefore_focus 0 ctrl t.slots hIlen0).mp $$ Hslots
      isimp only [hslotsGet0, Table.slotCell] at Hcell0
      ihave ⟨Hkey0, Hval0⟩ := Hcell0
      wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_xorI64]
      isimp only [full_of_and_xor]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_ctzI64 twp_wrapI64 twp_const twp_and twp_sub]
      isimp only [wrap_ctz_and_120 hm0mask hb0ne, slot_addr_step]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_const twp_add]
      isimp only [negFourAdd, valueAddr]
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr val0 hvv1 hvv2 hvv3
        with Hval0
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      isimp only [negEightAdd, keyAddr]
      wasm_twp_rebind Wasm.SmallStep.twp_load32_addr key0 hk1 hk2 hk3
        with Hkey0
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      ihave Hslots : Table.slotsBefore 0 ctrl t.slots $$
        [Hpre0 Hkey0 Hval0 Hpost0]
      · iapply (Table.slotsBefore_focus 0 ctrl t.slots hIlen0).mpr
        isimp only [hslotsGet0, Table.slotCell]
        iframe Hpre0 Hkey0 Hval0 Hpost0
      -- the marker call, WAT 1112
      iapply (marker_call (hlc := hlc)
        (walkLocals out (ctrl - UInt32.ofNat (64 * b0))
          (sp - 16) (UInt32.ofNat t.items)
          (ctrl + UInt32.ofNat (8 * (b0 + 1)))
          (Table.swarMatchFull (Table.groupWord (Table.groupAt t (8 * b0))))
          (UInt32.ofNat (8 * max t.items 4))
          (UInt32.ofNat (max t.items 4))
          (ctrl - UInt32.ofNat (8 * (8 * b0 +
            ctz64 64 (Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * b0)))) / 8)))
          val0 key0 0 0))
      isplitl_exact Hruntime
      · iintro Hruntime
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        wasm_twp_pures [twp_const]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        wasm_twp_pures [twp_localGet twp_const]
        -- the allocation, WAT 1115 to 1117
        have hmatches : AllocLayout.Matches (pairBlock (max t.items 4))
            (UInt32.ofNat (8 * max t.items 4)) 4 :=
          ⟨UInt32.toNat_ofNat_of_lt' hmulLt, rfl⟩
        have hvalid : AllocLayout.Valid (pairBlock (max t.items 4)) := by
          refine ⟨by simp only [pairBlock]; omega,
            by simp only [pairBlock]; omega,
            ⟨2, by simp only [pairBlock]; decide⟩,
            by simp only [pairBlock]; omega,
            by simp only [pairBlock]; omega,
            by simp only [pairBlock, UInt32.size]; omega,
            by simp only [pairBlock, UInt32.size]; omega⟩
        iapply (alloc_call (hlc := hlc)
          (walkLocals out (ctrl - UInt32.ofNat (64 * b0))
            (sp - 16) (UInt32.ofNat t.items)
            (ctrl + UInt32.ofNat (8 * (b0 + 1)))
            (Table.swarMatchFull (Table.groupWord (Table.groupAt t (8 * b0))))
            (UInt32.ofNat (8 * max t.items 4)) (UInt32.ofNat (max t.items 4))
            4 val0 key0 0 0)
          (UInt32.ofNat (8 * max t.items 4)) 4
          (pairBlock (max t.items 4)) heapId storedCursor frontier history
          input output raised)
        isplitl_exacts [Hruntime Hbump Hstreams]
        isplitl_pureexact ⟨hmatches, hvalid, Or.inr rfl⟩
        cases hdecision :
            classifyBump frontier (pairBlock (max t.items 4)) with
        | oom =>
            isimp only [AllocContinuation, hdecision]
            iintro Hbump Hstreams
            ihave Hoom := BI.and_elim_r $$ Hcont
            ihave Hoom := Hoom $$ %input
            iapply Hoom $$ Hstreams
        | success base finish =>
            isimp only [AllocContinuation, hdecision]
            isplit
            · iintro %bytes Hruntime Hbump Hblock Hstreams
              isimp only [ResumeWP, resumeExpr, List.nil_append,
                List.append_nil]
              iunfold LiveBlock at Hblock
              icases Hblock with ⟨Htoken, Hbytes, %hfacts⟩
              obtain ⟨hblen, hnonnull, halignFact⟩ := hfacts
              have hbytesLen : bytes.length = 8 * max t.items 4 := hblen
              isimp only [Slices.ByteSlice] at Hbytes
              icases Hbytes with ⟨%hbnowrap, Hraw⟩
              ihave Hbytes : Slices.ByteSlice 0 base bytes $$ [Hraw]
              · isimp only [Slices.ByteSlice]
                isplitl_pureexact hbnowrap
                · iexact Hraw
              have hbn : base.toNat + 8 * max t.items 4 < UInt32.size := by
                rw [← hbytesLen]; exact hbnowrap
              have htake8b : (bytes.take 8).length = 8 := by
                rw [List.length_take]; omega
              have happb := (Slices.ByteSlice_append
                (α := Universal.State) 0 base (bytes.take 8)
                (bytes.drop 8)).mp
              rw [List.take_append_drop, htake8b] at happb
              ihave ⟨Hhead0, Htail0⟩ := happb $$ Hbytes
              ihave ⟨%bw0, %bw1, Hb0, Hb1⟩ := outWords 0 base
                (bytes.take 8) htake8b (by omega) $$ Hhead0
              have hb4 := offset_facts base 4 4 rfl (by omega)
              have hb0f := offset_facts base 0 0 rfl (by omega)
              wasm_twp_localTee [List.set, List.length_cons,
                List.length_nil, Nat.reduceAdd, Nat.reduceSub]
              iapply Wasm.SmallStep.twp_eqz (result := 0)
                (by rw [if_neg hnonnull])
              wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet]
              wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := base)
                (offset := 4) bw1 hb4.1 hb4.2.1 hb4.2.2.1 hb4.2.2.2
                with Hb1
              wasm_twp_pures [twp_localGet twp_localGet]
              ihave Hb0 := wordMove32 (UInt32.add_zero _).symm $$ Hb0
              wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := base)
                (offset := 0) bw0 hb0f.1 hb0f.2.1 hb0f.2.2.1 hb0f.2.2.2
                with Hb0
              ihave Hb0 := wordMove32 (UInt32.add_zero _) $$ Hb0
              have hpushed1 : pushedAt t 1 = [(key0, val0)] := by
                unfold pushedAt
                rw [hfi]
                simp only [List.take_succ_cons, List.take_zero,
                  List.filterMap_cons, hslot0, List.filterMap_nil]
              ihave Hbuf : Table.PairSlice 0 base (pushedAt t 1) $$
                [Hb0 Hb1]
              · rw [hpushed1]
                isimp only [Table.PairSlice, Table.pairBytes_single]
                iapply (Table.ByteSlice_pair_as_words 0 base
                  (key0, val0)).mpr
                isplitl_pureexact (by omega)
                · iframe Hb0 Hb1
              -- the frame words, WAT 1127 to 1135
              isimp only [StackBelow] at Hbelow
              icases Hbelow with ⟨%hbelowLen0, Hbelow⟩
              ihave Hbelow : StackBelow sp (sortedEntriesDepth t.items)
                  below $$ [Hbelow]
              · isimp only [StackBelow]
                isplitl_pureexact hbelowLen0
                · iexact Hbelow
              ihave ⟨Hreserve, Hframe⟩ := below_split sp
                (sortedEntriesDepth t.items) 16 below hdeep
                (stack_split_addr sp _ hdeep) $$ Hbelow
              isimp only [StackBelow,
                show UInt32.ofNat 16 = (16 : UInt32) from rfl] at Hframe
              icases Hframe with ⟨%hframeLen, Hframe⟩
              ihave ⟨%hframeWords, Hcells⟩ :=
                ByteSlice_as_cells (sp - 16)
                  (below.drop (sortedEntriesDepth t.items - 16)) 4
                  (by omega) $$ Hframe
              obtain ⟨f0, f1, f2, f3, hfshape⟩ :=
                four_words _ hframeWords
              isimp only [hfshape, arrayAt] at Hcells
              icases Hcells with ⟨Hf0, Hf1, Hf2, Hf3, Hfemp⟩
              have hf8 : sp - 16 + 4 + 4 = sp - 16 + 8 := by
                rw [UInt32.add_assoc]; rfl
              have hf12 : sp - 16 + 4 + 4 + 4 = sp - 16 + 12 := by
                rw [UInt32.add_assoc, UInt32.add_assoc]; rfl
              have hc12 := offset_facts (sp - 16) 12 12 rfl (by omega)
              have hc8 := offset_facts (sp - 16) 8 8 rfl (by omega)
              have hc4 := offset_facts (sp - 16) 4 4 rfl (by omega)
              wasm_twp_pures [twp_localGet twp_const]
              ihave Hf3 := wordMove32 hf12 $$ Hf3
              wasm_twp_rebind Wasm.SmallStep.twp_store32
                (address := sp - 16) (offset := 12) f3
                hc12.1 hc12.2.1 hc12.2.2.1 hc12.2.2.2 with Hf3
              wasm_twp_pures [twp_localGet twp_localGet]
              ihave Hf2 := wordMove32 hf8 $$ Hf2
              wasm_twp_rebind Wasm.SmallStep.twp_store32
                (address := sp - 16) (offset := 8) f2
                hc8.1 hc8.2.1 hc8.2.2.1 hc8.2.2.2 with Hf2
              wasm_twp_pures [twp_localGet twp_localGet]
              wasm_twp_rebind Wasm.SmallStep.twp_store32
                (address := sp - 16) (offset := 4) f1
                hc4.1 hc4.2.1 hc4.2.2.1 hc4.2.2.2 with Hf1
              ihave Hf1 := wordMove32 rfl $$ Hf1
              ihave Hf2 := wordMove32 hf8.symm $$ Hf2
              ihave Hf3 := wordMove32 hf12.symm $$ Hf3
              ihave Hframe : arrayAt 0 (sp - 16)
                  [f0, UInt32.ofNat (max t.items 4), base, 1] $$
                [Hf0 Hf1 Hf2 Hf3]
              · isimp only [arrayAt]
                iframe Hf0 Hf1 Hf2 Hf3
              wasm_twp_pures [twp_block]
              simp only [pushBlock, List.drop_zero]
              wasm_twp_pures [twp_localGet twp_const twp_add]
              isimp only [negOneAdd, ofNat_sub_one hitemsPos hitemsLt]
              wasm_twp_localTee [List.set, List.length_cons,
                List.length_nil, Nat.reduceAdd, Nat.reduceSub]
              -- the exit that the three sort arms share
              have hdeepAddr : sp - 16 - UInt32.ofNat (sortDepth t.items)
                  = sp - UInt32.ofNat (sortedEntriesDepth t.items) := by
                rw [Table.sub_sub_addr, sortedEntriesDepth,
                  UInt32.ofNat_add]
                rfl
              have hcapNat : (UInt32.ofNat (max t.items 4)).toNat
                  = if t.items = 0 then 0 else max t.items 4 := by
                rw [if_neg hitems, UInt32.toNat_ofNat_of_lt' hcapLt]
              ihave Htail : TailExit t sp out ctrl base
                  (UInt32.ofNat (max t.items 4)) heapId
                  history.nextId finish finish.toNat
                  (history.allocate base (pairBlock (max t.items 4)))
                  input output raised
                  ({ locals := { callerLocals with values := stack },
                      continuation := code, resultArity := arity,
                      callerRemainder := remainder, control := controls,
                      returningInstance := { id := 0 } } :: calls)
                  s E Φ $$ [Hcont H0 H4 H8 H12 Hk0 Hk1]
              · isimp only [TailExit]
                iintro %l1 %l3 %l4 %l6' %l7' %l8' %l9' %l10' %l11' %w0 %w1
                  %w2 %w3 %m' %l12' %pairs %below' %hpost Hruntime Hsp
                  Hbelow Hcells Hout Hctrl Hslots Hbump Hvec Hstreams
                simp only [walkLocals, epilogue]
                wasm_twp_pures [twp_localGet twp_const twp_add]
                isimp only [StackPointer] at Hsp
                rw [hspBack]
                wasm_twp_rebind twp_globalSet with Hsp
                iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
                wasm_twp_rebind
                  Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
                simp only [List.take_zero, List.nil_append]
                iclose_map_runtime Hruntime with Hmodule Henv
                ihave Hsp : StackPointer sp $$ [Hsp]
                · isimp only [StackPointer]
                  iexact Hsp
                ihave Hframe16 : StackBelow sp 16
                    (WordCodec.u32le.serialize [w0, w1, w2, w3]) $$
                  [Hcells]
                · iapply StackBelow_of_cells sp (sp - 16) 16 4
                    [w0, w1, w2, w3] rfl rfl rfl (by omega)
                  iexact Hcells
                isimp only [StackBelow] at Hbelow
                icases Hbelow with ⟨%hbelowLen, Hbelow⟩
                ihave Hbelow := sliceMove hdeepAddr $$ Hbelow
                ihave Hbelow := below_join sp (sortedEntriesDepth t.items)
                  16 below' (WordCodec.u32le.serialize [w0, w1, w2, w3])
                  (by simp only [sortedEntriesDepth]; omega) hdeep
                  (stack_split_addr sp _ hdeep) $$
                  [Hbelow Hframe16]
                · iframe Hbelow Hframe16
                ihave Htable : Table.TableAt 0 map t $$
                  [H0 H4 H8 H12 Hctrl Hslots]
                · isimp only [Table.TableAt]
                  iexists ctrl
                  iright
                  isplitl_pureexact hbuckets1
                  · isimp only [Table.TableBody, Table.tableHeader]
                    isplitl_pureexact hctrlBound
                    · iframe H0 H4 H8 H12 Hctrl Hslots
                ihave Hmap : Table.HashMapAt 0 map k0 k1 t $$
                  [Htable Hk0 Hk1]
                · isimp only [Table.HashMapAt]
                  isplitl_exact Htable
                  · isplitl_exact Hk0
                    · iexact Hk1
                have hsortedEq : pairs = sortByKey (Table.toList t) :=
                  Table.eq_sortByKey_of_perm_of_sorted
                    hwf.toLayout.nodupKeys_toList hpost.1 hpost.2
                isimp only [hsortedEq] at Hvec
                ihave Hnormal := BI.and_elim_l $$ Hcont
                ihave Hnormal := Hnormal
                  $$ %(UInt32.ofNat (max t.items 4)) %base
                  %history.nextId %(below' ++ WordCodec.u32le.serialize
                    [w0, w1, w2, w3]) %finish %finish.toNat
                  %(history.allocate base (pairBlock (max t.items 4)))
                isimp only [ResumeWP, resumeExpr, List.nil_append] at
                  Hnormal
                iapply Hnormal $$ Hruntime Hsp Hbelow Hout Hmap Hbump Hvec
                  Hstreams %hcapNat
              -- the sort dispatch, WAT 1248 to 1281
              ihave Hsort : PushExit t ctrl (sp - 16) out base f0
                  (UInt32.ofNat (max t.items 4)) key0 (max t.items 4)
                  sortTail 0 [] tailFrames
                  ({ locals := { callerLocals with values := stack },
                      continuation := code, resultArity := arity,
                      callerRemainder := remainder, control := controls,
                      returningInstance := { id := 0 } } :: calls)
                  s E Φ $$
                [Htail Hout Hsp Hruntime Htoken Hbump Hstreams Hreserve]
              · isimp only [PushExit]
                iintro %b' %m' %l6' %l7' %l9' %l12' %spare %hspare Hctrl
                  Hslots Hframe Hbuf Hspare
                simp only [walkLocals, sortTail]
                isimp only [arrayAt] at Hframe
                icases Hframe with ⟨Hf0, Hf1, Hf2, Hf3, Hfe⟩
                ihave Hpair := (pointsTo_u32_pair_as_groupWord 0
                  (sp - 16 + 4) (UInt32.ofNat (max t.items 4)) base).mp $$
                  [Hf1 Hf2]
                · isplitl_exact Hf1
                  · irw_exact [hf8] with Hf2
                have hfl64 := offset_facts64 (sp - 16) 4 4 rfl (by omega)
                have ho064 := offset_facts64 out 0 0 rfl (by omega)
                have ho8w := offset_facts out 8 8 rfl (by omega)
                have hfc12 := offset_facts (sp - 16) 12 12 rfl (by omega)
                ihave ⟨%houtWords, Houtcells⟩ :=
                  ByteSlice_as_cells out outBefore 3 (by omega) $$ Hout
                obtain ⟨o0, o1, o2, houtShape⟩ := three_words _ houtWords
                isimp only [houtShape, arrayAt] at Houtcells
                icases Houtcells with ⟨Ho0, Ho1, Ho2, Hoe⟩
                wasm_twp_pures [twp_localGet twp_localGet]
                wasm_twp_rebind Wasm.SmallStep.twp_load64
                  (address := sp - 16) (offset := 4)
                  (wordPair (UInt32.ofNat (max t.items 4)) base)
                  hfl64.1 hfl64.2.1 hfl64.2.2.1 hfl64.2.2.2.1
                  hfl64.2.2.2.2.1 hfl64.2.2.2.2.2.1 hfl64.2.2.2.2.2.2.1
                  hfl64.2.2.2.2.2.2.2 with Hpair
                ihave Hopair := (pointsTo_u32_pair_as_groupWord 0 out o0
                  o1).mp $$ [Ho0 Ho1]
                · isplitl_exact Ho0
                  · iexact Ho1
                ihave Hopair := wordMove64 hout0.symm $$ Hopair
                wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out)
                  (offset := 0) (wordPair o0 o1) ho064.1 ho064.2.1
                  ho064.2.2.1 ho064.2.2.2.1 ho064.2.2.2.2.1
                  ho064.2.2.2.2.2.1 ho064.2.2.2.2.2.2.1
                  ho064.2.2.2.2.2.2.2 with Hopair
                ihave Hopair := wordMove64 hout0 $$ Hopair
                wasm_twp_pures [twp_localGet twp_localGet]
                ihave Hf3 := wordMove32 hf12 $$ Hf3
                wasm_twp_rebind Wasm.SmallStep.twp_load32
                  (address := sp - 16) (offset := 12)
                  (UInt32.ofNat (Table.fullIndices t).length) hfc12.1
                  hfc12.2.1 hfc12.2.2.1 hfc12.2.2.2 with Hf3
                wasm_twp_localTee [List.set, List.length_cons,
                  List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                ihave Ho2 := wordMove32 hout4 $$ Ho2
                wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out)
                  (offset := 8) o2 ho8w.1 ho8w.2.1 ho8w.2.2.1 ho8w.2.2.2
                  with Ho2
                have htoListLen : (Table.toList t).length
                    = (Table.fullIndices t).length := by
                  rw [← pushed_all hwf.toLayout,
                    pushed_length hwf.toLayout]
                  omega
                have hNlt : (Table.fullIndices t).length < UInt32.size := by
                  omega
                ihave ⟨Ho0, Ho1⟩ : iprop(pointsTo_u32 0 out
                    (UInt32.ofNat (max t.items 4)) ∗
                    pointsTo_u32 0 (out + 4) base) $$ [Hopair]
                · iapply (pointsTo_u32_pair_as_groupWord 0 out
                    (UInt32.ofNat (max t.items 4)) base).mpr
                  iexact Hopair
                ihave ⟨Hf1, Hf2⟩ : iprop(pointsTo_u32 0 (sp - 16 + 4)
                    (UInt32.ofNat (max t.items 4)) ∗
                    pointsTo_u32 0 (sp - 16 + 4 + 4) base) $$ [Hpair]
                · iapply (pointsTo_u32_pair_as_groupWord 0 (sp - 16 + 4)
                    (UInt32.ofNat (max t.items 4)) base).mpr
                  iexact Hpair
                ihave Hf3 := wordMove32 hf12.symm $$ Hf3
                ihave Hcells : arrayAt 0 (sp - 16)
                    [f0, UInt32.ofNat (max t.items 4), base,
                      UInt32.ofNat (Table.fullIndices t).length] $$
                  [Hf0 Hf1 Hf2 Hf3]
                · isimp only [arrayAt]
                  iframe Hf0 Hf1 Hf2 Hf3
                ihave Hbelow : StackBelow (sp - 16) (sortDepth t.items)
                    (below.take (sortedEntriesDepth t.items - 16)) $$
                  [Hreserve]
                · isimp only [StackBelow]
                  isplitl_pureexact (by
                    rw [List.length_take, hbelowLen0]
                    simp only [sortedEntriesDepth]
                    omega)
                  · irw_exact [hdeepAddr] with Hreserve
                ihave Hmkvec : iprop(∀ pairs : List (UInt32 × UInt32),
                    ⌜pairs.length = (Table.fullIndices t).length⌝ -∗
                    Table.PairSlice 0 base pairs -∗
                    PairVecAt heapId history.nextId
                      (UInt32.ofNat (max t.items 4)).toNat base pairs) $$
                  [Htoken Hspare]
                · iintro %pairs %hplen Hpairs
                  rw [UInt32.toNat_ofNat_of_lt' hcapLt]
                  iapply pairVec_of_slice heapId history.nextId
                    (max t.items 4) base pairs spare
                    (by omega) (by rw [hplen]; omega)
                    (by rw [hplen]; omega) hnonnull
                    (by simpa only [pairBlock] using halignFact)
                  isplitl_exact Htoken
                  · isplitl_exact Hpairs
                    · irw_exact [hplen] with Hspare
                ihave Hsp : StackPointer (sp - 16) $$ [Hsp]
                · isimp only [StackPointer]
                  iexact Hsp
                isimp only [TailExit] at Htail
                wasm_twp_pures [twp_localGet twp_const]
                by_cases hNsmall : (Table.fullIndices t).length < 2
                · -- one entry, WAT 1257 to 1258
                  have hlt : UInt32.ofNat (Table.fullIndices t).length
                      < (2 : UInt32) := by
                    rw [UInt32.lt_iff_toNat_lt,
                      UInt32.toNat_ofNat_of_lt' hNlt,
                      show (2 : UInt32).toNat = 2 from rfl]
                    omega
                  iapply Wasm.SmallStep.twp_ltU (result := 1)
                    (by rw [if_pos hlt])
                  iapply Wasm.SmallStep.twp_brIf
                    (by decide : (1 : UInt32) ≠ 0) (by rfl)
                  simp only [List.take_zero, List.nil_append]
                  ihave Hvec := Hmkvec $$ %(Table.toList t) %htoListLen
                    Hbuf
                  ihave Ho2 := wordMove32 hout4.symm $$ Ho2
                  ihave Houtb : Slices.ByteSlice 0 out
                      (WordCodec.u32le.serialize
                        [UInt32.ofNat (max t.items 4), base,
                          UInt32.ofNat t.items]) $$ [Ho0 Ho1 Ho2]
                  · isimp only [hNitems] at Ho2
                    iapply ByteSlice_of_cells out
                      [UInt32.ofNat (max t.items 4), base,
                        UInt32.ofNat t.items] (by simp only
                          [List.length_cons, List.length_nil]; omega)
                    isimp only [arrayAt]
                    iframe Ho0 Ho1 Ho2
                  ihave Hgo := Htail
                    $$ %(UInt32.ofNat (Table.fullIndices t).length)
                    %(UInt32.ofNat (Table.fullIndices t).length)
                    %(ctrl + UInt32.ofNat (8 * (b' + 1))) %l6' %l7'
                    %(0 : UInt32) %l9' %key0 %base %f0
                    %(UInt32.ofNat (max t.items 4)) %base
                    %(UInt32.ofNat (Table.fullIndices t).length) %m' %l12'
                    %(Table.toList t)
                    %(below.take (sortedEntriesDepth t.items - 16))
                    %(⟨List.Perm.refl _,
                      sorted_of_length_le_one (by omega)⟩ :
                      (Table.toList t).Perm (Table.toList t) ∧
                        Table.SortedByKey (Table.toList t))
                    Hruntime Hsp Hbelow Hcells Houtb Hctrl Hslots Hbump
                    Hvec Hstreams
                  iexact Hgo
                · -- two entries or more, WAT 1259 to 1281
                  have hnlt : ¬ UInt32.ofNat (Table.fullIndices t).length
                      < (2 : UInt32) := by
                    rw [UInt32.lt_iff_toNat_lt,
                      UInt32.toNat_ofNat_of_lt' hNlt,
                      show (2 : UInt32).toNat = 2 from rfl]
                    omega
                  have hlenNat : (UInt32.ofNat
                      (Table.fullIndices t).length).toNat
                      = (Table.fullIndices t).length :=
                    UInt32.toNat_ofNat_of_lt' hNlt
                  iapply Wasm.SmallStep.twp_ltU (result := 0)
                    (by rw [if_neg hnlt])
                  wasm_twp_pures [twp_brIfZero twp_localGet]
                  have ho4w := offset_facts out 4 4 rfl (by omega)
                  wasm_twp_rebind Wasm.SmallStep.twp_load32
                    (address := out) (offset := 4) base ho4w.1 ho4w.2.1
                    ho4w.2.2.1 ho4w.2.2.2 with Ho1
                  wasm_twp_localSet [List.set, List.length_cons,
                    List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                  wasm_twp_pures [twp_block]
                  simp only [sortBlock, List.drop_zero]
                  isimp only [hNitems] at Ho2
                  ihave Ho2 := wordMove32 hout4.symm $$ Ho2
                  ihave Houtb : Slices.ByteSlice 0 out
                      (WordCodec.u32le.serialize
                        [UInt32.ofNat (max t.items 4), base,
                          UInt32.ofNat t.items]) $$ [Ho0 Ho1 Ho2]
                  · iapply ByteSlice_of_cells out
                      [UInt32.ofNat (max t.items 4), base,
                        UInt32.ofNat t.items] (by simp only
                          [List.length_cons, List.length_nil]; omega)
                    isimp only [arrayAt]
                    iframe Ho0 Ho1 Ho2
                  wasm_twp_pures [twp_localGet twp_const]
                  by_cases hSmall : (Table.fullIndices t).length < 21
                  · -- the insertion sort, WAT 1276 to 1280
                    have hlt21 : UInt32.ofNat (Table.fullIndices t).length
                        < (21 : UInt32) := by
                      rw [UInt32.lt_iff_toNat_lt, hlenNat,
                        show (21 : UInt32).toNat = 21 from rfl]
                      omega
                    iapply Wasm.SmallStep.twp_ltU (result := 1)
                      (by rw [if_pos hlt21])
                    iapply Wasm.SmallStep.twp_brIf
                      (by decide : (1 : UInt32) ≠ 0) (by rfl)
                    simp only [List.take_zero, List.nil_append]
                    wasm_twp_pures [twp_localGet twp_localGet twp_const]
                    iapply (sort15_call (hlc := hlc)
                      (walkLocals out
                        (UInt32.ofNat (Table.fullIndices t).length)
                        (sp - 16)
                        (UInt32.ofNat (Table.fullIndices t).length) base m'
                        l6' l7' 0 l9' key0 base l12')
                      base (UInt32.ofNat (Table.fullIndices t).length) 1
                      (Table.toList t))
                    isplitl_exact Hruntime
                    · isplitl_exact Hbuf
                      · isplitl_pureexact ⟨by rw [htoListLen, hlenNat],
                          by decide, by
                            rw [hlenNat, show (1 : UInt32).toNat = 1 from
                              rfl]
                            omega,
                          sorted_of_length_le_one (by
                            rw [List.length_take,
                              show (1 : UInt32).toNat = 1 from rfl]
                            omega),
                          by rw [hlenNat]; omega⟩
                        · isimp only [SortPostFrameless]
                          iintro %sortedOut Hruntime Hbuf %hpost
                          isimp only [ResumeWP, resumeExpr,
                            List.nil_append]
                          iapply Wasm.SmallStep.twp_br (by rfl)
                          simp only [List.take_zero, List.nil_append]
                          have hsortLen : sortedOut.length
                              = (Table.fullIndices t).length := by
                            rw [hpost.1.length_eq, htoListLen]
                          ihave Hvec := Hmkvec $$ %sortedOut %hsortLen
                            Hbuf
                          ihave Hgo := Htail
                            $$ %(UInt32.ofNat
                              (Table.fullIndices t).length)
                            %(UInt32.ofNat (Table.fullIndices t).length)
                            %base %l6' %l7' %(0 : UInt32) %l9' %key0 %base
                            %f0 %(UInt32.ofNat (max t.items 4)) %base
                            %(UInt32.ofNat (Table.fullIndices t).length)
                            %m' %l12' %sortedOut
                            %(below.take (sortedEntriesDepth t.items - 16))
                            %hpost Hruntime Hsp Hbelow Hcells Houtb Hctrl
                            Hslots Hbump Hvec Hstreams
                          iexact Hgo
                  · -- the quicksort, WAT 1269 to 1274
                    have hnlt21 :
                        ¬ UInt32.ofNat (Table.fullIndices t).length
                          < (21 : UInt32) := by
                      rw [UInt32.lt_iff_toNat_lt, hlenNat,
                        show (21 : UInt32).toNat = 21 from rfl]
                      omega
                    iapply Wasm.SmallStep.twp_ltU (result := 0)
                      (by rw [if_neg hnlt21])
                    wasm_twp_pures [twp_brIfZero twp_localGet twp_localGet
                      twp_localGet twp_const twp_add]
                    ihave Hbelow := (show StackBelow (sp - 16)
                        (sortDepth t.items)
                        (below.take (sortedEntriesDepth t.items - 16))
                      ⊢ StackBelow (sp - 16)
                        (sortDepth (UInt32.ofNat
                          (Table.fullIndices t).length).toNat)
                        (below.take (sortedEntriesDepth t.items - 16))
                      from by rw [hlenNat, hNitems]) $$ Hbelow
                    iapply (sort14_call (hlc := hlc)
                      (walkLocals out
                        (UInt32.ofNat (Table.fullIndices t).length)
                        (sp - 16)
                        (UInt32.ofNat (Table.fullIndices t).length) base m'
                        l6' l7' 0 l9' key0 base l12')
                      (sp - 16) base
                      (UInt32.ofNat (Table.fullIndices t).length)
                      (4 + (sp - 16)) (Table.toList t)
                      (below.take (sortedEntriesDepth t.items - 16)))
                    isplitl_exact Hruntime
                    · isplitl_exact Hsp
                      · isplitl_exact Hbelow
                        · isplitl_exact Hbuf
                          · isplitl_pureexact
                              ⟨by rw [htoListLen, hlenNat],
                                hwf.toLayout.nodupKeys_toList,
                                by rw [hlenNat, hNitems]; omega,
                                by rw [hlenNat]; omega,
                                by
                                  rw [hlenNat, hNitems]
                                  simp only [sortedEntriesDepth] at hdepth
                                  omega⟩
                            · isimp only [SortPost]
                              iintro %sortedOut %belowAfter Hruntime Hsp
                                Hbelow Hbuf Hemp %hpost
                              isimp only [ResumeWP, resumeExpr,
                                List.nil_append]
                              iapply Wasm.SmallStep.twp_br (by rfl)
                              simp only [List.take_zero, List.nil_append]
                              have hsortLen : sortedOut.length
                                  = (Table.fullIndices t).length := by
                                rw [hpost.1.length_eq, htoListLen]
                              ihave Hvec := Hmkvec $$ %sortedOut
                                %hsortLen Hbuf
                              ihave Hbelow := (show StackBelow (sp - 16)
                                  (sortDepth (UInt32.ofNat
                                    (Table.fullIndices t).length).toNat)
                                  belowAfter
                                ⊢ StackBelow (sp - 16) (sortDepth t.items)
                                  belowAfter
                                from by rw [hlenNat, hNitems]) $$ Hbelow
                              ihave Hgo := Htail
                                $$ %(UInt32.ofNat
                                  (Table.fullIndices t).length)
                                %(UInt32.ofNat
                                  (Table.fullIndices t).length)
                                %base %l6' %l7' %(0 : UInt32) %l9' %key0
                                %base %f0 %(UInt32.ofNat (max t.items 4))
                                %base %(UInt32.ofNat
                                  (Table.fullIndices t).length)
                                %m' %l12' %sortedOut %belowAfter
                                %hpost Hruntime Hsp Hbelow Hcells Houtb
                                Hctrl Hslots Hbump Hvec Hstreams
                              iexact Hgo
              by_cases hone : t.items = 1
              · -- the table holds one entry, WAT 1137 to 1141
                isimp only [PushExit, hNitems] at Hsort
                have hz : UInt32.ofNat (t.items - 1) = (0 : UInt32) := by
                  rw [hone]
                  rfl
                have hone32 : UInt32.ofNat t.items = (1 : UInt32) := by
                  rw [hone]
                  rfl
                have hbuf1 : Table.toList t = pushedAt t 1 := by
                  rw [← pushed_all hwf.toLayout, hNitems, hone]
                have haddr1 : UInt32.ofNat (8 * t.items)
                    = UInt32.ofNat 8 := by
                  rw [hone]
                iapply Wasm.SmallStep.twp_eqz (result := 1)
                  (by rw [if_pos hz])
                iapply Wasm.SmallStep.twp_brIf
                  (by decide : (1 : UInt32) ≠ 0) (by rfl)
                simp only [List.take_zero, List.nil_append, hz]
                ihave Hframe := (show arrayAt (α := Universal.State) 0
                      (sp - 16)
                      [f0, UInt32.ofNat (max t.items 4), base, 1]
                    ⊢ arrayAt 0 (sp - 16)
                      [f0, UInt32.ofNat (max t.items 4), base,
                        UInt32.ofNat t.items]
                  from by rw [hone32]) $$ Hframe
                ihave Hbuf := (show Table.PairSlice (α := Universal.State)
                      0 base (pushedAt t 1)
                    ⊢ Table.PairSlice 0 base (Table.toList t)
                  from by rw [hbuf1]) $$ Hbuf
                ihave Htail0 := (show Slices.ByteSlice
                      (α := Universal.State) 0 (base + UInt32.ofNat 8)
                      (bytes.drop 8)
                    ⊢ Slices.ByteSlice 0
                      (base + UInt32.ofNat (8 * t.items)) (bytes.drop 8)
                  from by rw [haddr1]) $$ Htail0
                ihave Hgo := Hsort $$ %b0
                  %(Table.swarMatchFull
                    (Table.groupWord (Table.groupAt t (8 * b0))))
                  %(UInt32.ofNat (8 * max t.items 4))
                  %(UInt32.ofNat (max t.items 4)) %val0 %(0 : UInt64)
                  %(bytes.drop 8)
                  %(show (bytes.drop 8).length
                      = 8 * max t.items 4 - 8 * t.items by
                    rw [List.length_drop, hbytesLen, hone])
                  Hctrl Hslots Hframe Hbuf Htail0
                iexact Hgo
              · -- the table holds two entries or more, WAT 1142 to 1150
                have hzne : UInt32.ofNat (t.items - 1) ≠ (0 : UInt32) :=
                  ofNat_ne_zero (by omega) (by omega)
                iapply Wasm.SmallStep.twp_eqz (result := 0)
                  (by rw [if_neg hzne])
                wasm_twp_pures [twp_brIfZero twp_localGet twp_constI64
                  twp_addI64 twp_localGet twp_andI64_bits]
                wasm_twp_localSet [List.set, List.length_cons,
                  List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                wasm_twp_pures [twp_const]
                wasm_twp_localSet [List.set, List.length_cons,
                  List.length_nil, Nat.reduceAdd, Nat.reduceSub]
                have hcomm : (Table.swarMatchFull
                      (Table.groupWord (Table.groupAt t (8 * b0)))
                    + 18446744073709551615) &&&
                      Table.swarMatchFull
                        (Table.groupWord (Table.groupAt t (8 * b0)))
                  = Table.swarMatchFull
                      (Table.groupWord (Table.groupAt t (8 * b0))) &&&
                    (Table.swarMatchFull
                      (Table.groupWord (Table.groupAt t (8 * b0)))
                      + 18446744073709551615) := UInt64.and_comm _ _
                have hl8 : UInt32.ofNat (t.items - 1)
                    = UInt32.ofNat ((Table.fullIndices t).length - 1) := by
                  rw [hNitems]
                simp only [hcomm, hl8]
                ihave Hexit : PushExit t ctrl (sp - 16) out base f0
                    (UInt32.ofNat (max t.items 4)) key0 (max t.items 4)
                    [] 0 [] (pushFrame :: tailFrames)
                    ({ locals := { callerLocals with values := stack },
                        continuation := code, resultArity := arity,
                        callerRemainder := remainder, control := controls,
                        returningInstance := { id := 0 } } :: calls)
                    s E Φ $$ [Hsort]
                · isimp only [PushExit]
                  iintro %b' %m' %l6' %l7' %l9' %l12' %spare %hspare Hctrl
                    Hslots Hframe Hbuf Hspare
                  wasm_twp_pures [twp_exitControl]
                  simp only [List.take_zero, List.nil_append]
                  isimp only [PushExit] at Hsort
                  ihave Hgo := Hsort $$ %b' %m' %l6' %l7' %l9' %l12'
                    %spare %hspare Hctrl Hslots Hframe Hbuf Hspare
                  iexact Hgo
                iapply twp_pushLoop hwf.toLayout ctrl (sp - 16) out base f0
                  (UInt32.ofNat (max t.items 4)) key0 (max t.items 4)
                  ⟨1, b0,
                    Table.swarMatchFull
                        (Table.groupWord (Table.groupAt t (8 * b0))) &&&
                      (Table.swarMatchFull
                        (Table.groupWord (Table.groupAt t (8 * b0)))
                        + 18446744073709551615),
                    UInt32.ofNat (8 * max t.items 4),
                    UInt32.ofNat (max t.items 4), val0, 0⟩
                  hctrlBound rfl (by omega) hcapLt (by omega) (by omega)
                isplitl [Hctrl Hslots Hframe Hbuf Htail0]
                · isimp only [PushInv]
                  isplitl_pureexact
                    (⟨by omega, by omega, hb0lt,
                      iterNext_and_REP80 hm0mask, by
                        rw [hfi]
                        rfl⟩ :
                      1 < (Table.fullIndices t).length ∧ 1 ≤ 1 ∧
                        b0 < numGroups t ∧
                        (Table.swarMatchFull
                            (Table.groupWord (Table.groupAt t (8 * b0)))
                          &&& (Table.swarMatchFull
                            (Table.groupWord (Table.groupAt t (8 * b0)))
                            + 18446744073709551615)) &&& Table.REP80
                          = Table.swarMatchFull
                              (Table.groupWord
                                (Table.groupAt t (8 * b0))) &&&
                            (Table.swarMatchFull
                              (Table.groupWord (Table.groupAt t (8 * b0)))
                              + 18446744073709551615) ∧
                        walkRest t b0
                            (Table.swarMatchFull
                              (Table.groupWord
                                (Table.groupAt t (8 * b0))) &&&
                              (Table.swarMatchFull
                                (Table.groupWord
                                  (Table.groupAt t (8 * b0)))
                                + 18446744073709551615))
                          = (Table.fullIndices t).drop 1)
                  · isplitl_exact Hctrl
                    · isplitl_exact Hslots
                      · isplitl_exact Hframe
                        · isplitl_exact Hbuf
                          · iexists (bytes.drop 8)
                            isplitl_pureexact
                              (show (bytes.drop 8).length
                                  = 8 * max t.items 4 - 8 * 1 by
                                rw [List.length_drop, hbytesLen])
                            · iexact Htail0
                · iexact Hexit
            · iintro Hbump Hstreams
              ihave Hoom := BI.and_elim_r $$ Hcont
              ihave Hoom := Hoom $$ %input
              iapply Hoom $$ Hstreams

end Project.RustHashMap.Func4Proof
