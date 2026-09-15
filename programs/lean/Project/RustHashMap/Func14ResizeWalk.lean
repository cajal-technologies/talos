import Project.RustHashMap.ResizePures
import Project.RustHashMap.LookupPures
import Project.RustHashMap.FrameCells
import Project.RustHashMap.Func15Insert

/-!
# The hash and the buckets of the resize walk of absolute `func 17`

The walk of WAT lines 3746 to 4083 of
`programs/rust/build/rust_hash_map/program.wat` moves every full bucket of
the old table into the fresh one.  It hashes the key of each bucket again,
and the compiler hoisted every part of the first SipRound that does not
read the key out of the loop, to WAT lines 3750 to 3795.

`CodeLib.RustStd.HashMap.SipHoist` holds the model of that split.  This
module reads the compiled form of both halves.

* `hoistWasm` is the block above the loop, WAT 3752 to 3795.
  `hoistWasm_eq` identifies it with `SipHash.hoist`.
* `resizeCompress` is the first part of the loop body, WAT 3841 to 3885.
  `resizeCompress_eq` identifies it with `SipHash.stateFromHoist`.
* `resizeInlineHash` is the whole hash of one turn, WAT 3841 to 3976.
  `resizeInlineHash_eq` identifies it with `SipHash.hashU32Low`.

The three finalize rounds have the same operand order as the two lookup
kernels, so the round shapes come from
`Project.RustHashMap.LookupPures`.  As in the lookup lane, the compiled
run ends with `i64.shr_u 32` where the model rotates, so the bridge goes
to `SipHash.hashU32Low` and not to `SipHash.hashU32`.  Compose it with
`Table.h1_hashU32Low` and `Table.h2_hashU32Low` to speak about the model
hash.

The second half of the module reads one bucket of the old table and one
bucket of the fresh table as one owned `u64`.  WAT 4074 to 4080 copies a
bucket with one `i64.load align=1` and one `i64.store`, so the proof needs
the eight bytes of a bucket as a block and never as bits.
-/

namespace Project.RustHashMap.Func14ResizeWalk

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd.HashMap
open Wasm.RustStd.HashMap.Table
open Project.RustHashMap.Contracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open scoped Wasm.SmallStep.Outcome

/-! ## The hoisted block, WAT 3752 to 3795 -/

/-- The six words that WAT 3752 to 3795 computes once, above the loop.
`k0` is the word at the `RandomState` pointer and `k1` is the word eight
bytes above it. -/
def hoistWasm (k0 k1 : UInt64) : SipHash.Hoist :=
  let v1 := k1 ^^^ 7237128888997146477
  let sum01 := v1 + (k0 ^^^ 8317987319222330741)
  let mid1 := SipHash.rotl v1 13 ^^^ sum01
  { sum01 := sum01
    rot0 := SipHash.rotl sum01 32
    mid1 := mid1
    pre1 := SipHash.rotl mid1 17
    base3 := k1 ^^^ 8098989879002948979
    base2 := k0 ^^^ 7816392313619706465 }

/-- The compiled block is the model hoist.  The constant of local 21 is
the `v3` constant of `SipHash.init` with the length byte folded in. -/
theorem hoistWasm_eq (k0 k1 : UInt64) :
    hoistWasm k0 k1 = SipHash.hoist k0 k1 := by
  have hc3 : (8098989879002948979 : UInt64)
      = (0x7465646279746573 : UInt64) ^^^ (0x0400000000000000 : UInt64) := by
    decide
  unfold hoistWasm SipHash.hoist SipHash.init
  simp only [hc3, UInt64.xor_assoc, UInt64.add_comm]


/-! ## The hash of one turn, WAT 3841 to 3976 -/

/-- The state that WAT 3841 to 3885 builds for one key, in the operand
order of the two pushes. -/
def resizeCompress (h : SipHash.Hoist) (key : UInt32) : SipHash.State :=
  let key64 : UInt64 := key.toUInt64
  let w3 := key64 ^^^ h.base3
  let a2 := w3 + h.base2
  let c3 := SipHash.rotl w3 16 ^^^ a2
  let c0 := c3 + h.rot0
  let b2 := h.mid1 + a2
  { v0 := c0 ^^^ (key64 ||| 288230376151711744)
    v1 := b2 ^^^ h.pre1
    v2 := SipHash.rotl b2 32
    v3 := SipHash.rotl c3 21 ^^^ c0 }

/-- The compiled state is the model state.  The `i64.or` of the length
byte is the `xor` of the model, because a `u32` key has no bit at 58. -/
theorem resizeCompress_eq (h : SipHash.Hoist) (key : UInt32) :
    resizeCompress h key = SipHash.stateFromHoist h key.toUInt64 := by
  have hkey : (key.toUInt64).toNat < 2 ^ 32 := by
    rw [UInt32.toNat_toUInt64]
    exact key.toNat_lt
  have hor : (key.toUInt64 ||| 288230376151711744 : UInt64)
      = (0x0400000000000000 : UInt64) ^^^ key.toUInt64 := by
    rw [UInt64.or_comm]
    exact SipHash.or_lengthByte_eq_xor hkey
  unfold resizeCompress SipHash.stateFromHoist
  simp only [hor, UInt64.xor_assoc, UInt64.xor_comm, xor_left_comm,
    UInt64.add_comm]

/-- The whole `i64` run of one turn of the walk, WAT 3841 to 3976. -/
def resizeInlineHash (h : SipHash.Hoist) (key : UInt32) : UInt64 :=
  let s := resizeCompress h key
  finalWasm (roundWasm2 (roundWasm1 { s with v2 := s.v2 ^^^ 255 }))

/-- The compiled run is the compiled hash of the key. -/
theorem resizeInlineHash_eq (k0 k1 : UInt64) (key : UInt32) :
    resizeInlineHash (SipHash.hoist k0 k1) key
      = SipHash.hashU32Low k0 k1 key := by
  rw [hashU32Low_eq_compress, SipHash.compress_eq_stateFromHoist]
  unfold resizeInlineHash SipHash.finalizeLow
  simp only [resizeCompress_eq, roundWasm1_eq, roundWasm2_eq, finalWasm_eq]

/-- The compiled run gives the start position that the model gives. -/
theorem resizeInlineHash_h1 (k0 k1 : UInt64) (key : UInt32) :
    Table.h1 (resizeInlineHash (SipHash.hoist k0 k1) key)
      = Table.h1 (SipHash.hashU32 k0 k1 key) := by
  rw [resizeInlineHash_eq, Table.h1_hashU32Low]

/-- The compiled run gives the control byte that the model gives. -/
theorem resizeInlineHash_h2 (k0 k1 : UInt64) (key : UInt32) :
    Table.h2 (resizeInlineHash (SipHash.hoist k0 k1) key)
      = Table.h2 (SipHash.hashU32 k0 k1 key) := by
  rw [resizeInlineHash_eq, Table.h2_hashU32Low]

/-! ## One bucket as one owned double word -/

section Bucket

variable {α : Type} [WasmHeapGS α]

/-- A full bucket is one owned `u64`.  WAT 4074 to 4080 copies a bucket
with one `i64.load align=1` and one `i64.store`. -/
theorem slotCell_some_as_u64 (memId : Nat) (addr : UInt32)
    (key value : UInt32) :
    Table.slotCell (α := α) memId addr (some (key, value)) ⊣⊢
      pointsTo_u64 memId addr (wordPair key value) := by
  unfold Table.slotCell
  exact pointsTo_u32_pair_as_groupWord memId addr key value

/-- An empty bucket lends eight bytes as one owned `u64`. -/
theorem slotCell_none_to_u64 (memId : Nat) (addr : UInt32) :
    Table.slotCell (α := α) memId addr none ⊢
      iprop(∃ w : UInt64, pointsTo_u64 memId addr w) := by
  iintro Hcell
  icases (Table.slotCell_none_as_words memId addr).mp $$ Hcell with
    ⟨%key, %value, Hkey, Hvalue⟩
  iexists wordPair key value
  iapply (pointsTo_u32_pair_as_groupWord memId addr key value).mp
  isplitl [Hkey]
  · iexact Hkey
  · iexact Hvalue

end Bucket

/-- Move an owned double word between two names of one address. -/
theorem wordMove64 [WasmHeapGS Universal.State]
    {address target : UInt32} {word : UInt64} (haddress : target = address) :
    pointsTo_u64 0 address word ⊢ pointsTo_u64 0 target word := by
  rw [haddress]

/-! ## The shape of the walk in the compiled body

The walk sits inside seven blocks of absolute `func 17`.  The path here is
the one that `Project.RustHashMap.Func14Proof` takes, down to the block at
WAT 3746 that the item count guards. -/

/-- The body of the `block` instruction at index `i` of `p`. -/
def blockAt (p : Program) (i : Nat) : Program :=
  match p[i]? with
  | some (.block _ _ body) => body
  | _ => []

/-- The body of the `loop` instruction at index `i` of `p`. -/
def loopAt (p : Program) (i : Nat) : Program :=
  match p[i]? with
  | some (.loop _ _ body) => body
  | _ => []

/-- WAT 3021 to 4130, inside the first block. -/
def blockOne : Program := blockAt Project.RustHashMap.func14 5

/-- WAT 3021 to 4118. -/
def blockTwo : Program := blockAt blockOne 0

/-- WAT 3729 to 4117. -/
def commitMid : Program := (blockTwo.drop 1).drop 5

/-- WAT 3747 to 4083, the block that the item count guards. -/
def blockResize : Program := blockAt commitMid 17

/-- WAT 3750 to 4083. -/
def resizeTail : Program := blockResize.drop 3

/-- WAT 3797 to 4082, the body of the walk loop. -/
def walkBody : Program := loopAt resizeTail 46

/-- WAT 3798 to 3822, the group advance. -/
def advBody : Program := blockAt walkBody 0

/-- WAT 3825 to 4012, the hash and the insert probe. -/
def hashBody : Program := blockAt walkBody 1

/-- WAT 4019 to 4043, the mirror fix. -/
def fixBody : Program := blockAt walkBody 6

/-- WAT 3750 to 3795: the two seed words, the five hoisted words, the first
group mask and the three loop registers. -/
@[reducible] def hoistPhase (contCode : Program) : Program :=
    Instruction.localGet 3 :: .load64 8 :: .localTee 13 ::
    .constI64 7237128888997146477 :: .xorI64 :: .localTee 14 :: .localGet 3 ::
    .load64 0 :: .localTee 15 :: .constI64 8317987319222330741 :: .xorI64 ::
    .addI64 :: .localTee 16 :: .constI64 32 :: .rotlI64 :: .localSet 18 ::
    .localGet 14 :: .constI64 13 :: .rotlI64 :: .localGet 16 :: .xorI64 ::
    .localTee 19 :: .constI64 17 :: .rotlI64 :: .localSet 20 :: .localGet 13 ::
    .constI64 8098989879002948979 :: .xorI64 :: .localSet 21 :: .localGet 15 ::
    .constI64 7816392313619706465 :: .xorI64 :: .localSet 26 :: .localGet 10 ::
    .load64 0 :: .constI64 18446744073709551615 :: .xorI64 ::
    .constI64 9259542123273814144 :: .andI64 :: .localSet 13 :: .localGet 10 ::
    .localSet 4 :: .const 0 :: .localSet 2 :: .localGet 6 :: .localSet 3 ::
    contCode

/-- WAT 3825 to 3842: the address of the old bucket and its key. -/
@[reducible] def addrPhase (contCode : Program) : Program :=
    Instruction.localGet 9 :: .localGet 11 :: .localGet 10 :: .localGet 13 ::
    .ctzI64 :: .wrapI64 :: .const 3 :: .shrU :: .localGet 2 :: .add ::
    .const 3 :: .shl :: .sub :: .const 4294967288 :: .add :: .localTee 22 ::
    .load32UI64 0 :: .localTee 14 :: contCode

set_option maxRecDepth 1048576 in
/-- The hoisted block and the walk loop are the whole guarded region. -/
theorem shape_resize_tail :
    resizeTail = hoistPhase [.loop 0 0 walkBody] := by rfl

set_option maxRecDepth 1048576 in
/-- The body of the walk loop: the group advance, the hash with the insert
probe, the mask step, the mirror fix and the writes. -/
theorem shape_walk_body :
    walkBody = .block 0 0 advBody :: .block 0 0 hashBody ::
      .localGet 13 :: .constI64 18446744073709551615 :: .addI64 ::
      .localSet 15 :: .block 0 0 fixBody :: walkBody.drop 7 := by rfl

/-! ## The compiled hash region, WAT 3843 to 3976 -/

/-- The `i64` run of one turn of the walk.  The key is already in local 14
and on the operand stack, and the five hoisted words sit in locals 18, 19,
20, 21 and 26. -/
@[reducible] def resizeHashPhase (contCode : Program) : Program :=
    Instruction.localGet 21 :: .xorI64 :: .localTee 15 :: .constI64 16 ::
    .rotlI64 :: .localGet 15 :: .localGet 26 :: .addI64 :: .localTee 15 ::
    .xorI64 :: .localTee 16 :: .localGet 18 :: .addI64 :: .localTee 24 ::
    .localGet 14 :: .constI64 288230376151711744 :: .orI64 :: .xorI64 ::
    .localGet 19 :: .localGet 15 :: .addI64 :: .localTee 14 :: .localGet 20 ::
    .xorI64 :: .localTee 15 :: .addI64 :: .localTee 17 :: .localGet 15 ::
    .constI64 13 :: .rotlI64 :: .xorI64 :: .localTee 15 :: .localGet 14 ::
    .constI64 32 :: .rotlI64 :: .constI64 255 :: .xorI64 :: .localGet 16 ::
    .constI64 21 :: .rotlI64 :: .localGet 24 :: .xorI64 :: .localTee 14 ::
    .addI64 :: .localTee 16 :: .addI64 :: .localTee 24 :: .localGet 15 ::
    .constI64 17 :: .rotlI64 :: .xorI64 :: .localTee 15 :: .constI64 13 ::
    .rotlI64 :: .localGet 15 :: .localGet 16 :: .localGet 14 :: .constI64 16 ::
    .rotlI64 :: .xorI64 :: .localTee 14 :: .localGet 17 :: .constI64 32 ::
    .rotlI64 :: .addI64 :: .localTee 16 :: .addI64 :: .localTee 15 ::
    .xorI64 :: .localTee 17 :: .constI64 17 :: .rotlI64 :: .localGet 17 ::
    .localGet 14 :: .constI64 21 :: .rotlI64 :: .localGet 16 :: .xorI64 ::
    .localTee 14 :: .localGet 24 :: .constI64 32 :: .rotlI64 :: .addI64 ::
    .localTee 16 :: .addI64 :: .localTee 24 :: .xorI64 :: .localTee 17 ::
    .constI64 13 :: .rotlI64 :: .localGet 17 :: .localGet 14 :: .constI64 16 ::
    .rotlI64 :: .localGet 16 :: .xorI64 :: .localTee 14 :: .localGet 15 ::
    .constI64 32 :: .rotlI64 :: .addI64 :: .localTee 15 :: .addI64 ::
    .xorI64 :: .localTee 16 :: .constI64 17 :: .rotlI64 :: .localGet 14 ::
    .constI64 21 :: .rotlI64 :: .localGet 15 :: .xorI64 :: .localTee 14 ::
    .constI64 16 :: .rotlI64 :: .localGet 14 :: .localGet 24 :: .constI64 32 ::
    .rotlI64 :: .addI64 :: .localTee 14 :: .xorI64 :: .constI64 21 ::
    .rotlI64 :: .xorI64 :: .localGet 16 :: .localGet 14 :: .addI64 ::
    .localTee 14 :: .constI64 32 :: .shrUI64 :: .xorI64 :: .localGet 14 ::
    .xorI64 :: contCode

/-- The probe of the hash block, WAT 3977 to 4012. -/
def hashTail : Program := hashBody.drop 152

set_option maxRecDepth 1048576 in
/-- The hash region is the slice of the probe block that `addrPhase`
leaves. -/
theorem shape_hash_body :
    hashBody = addrPhase (resizeHashPhase hashTail) := by rfl

/-- The twenty-three locals of absolute `func 17`.  Index `i` of the list
is wasm local `i + 5`. -/
@[reducible] def rawLocals (l5 l6 l7 l8 l9 l10 l11 l12 w13 w14 w15 w16 w17
    w18 w19 w20 w21 l22 l23 w24 l25 w26 l27 : Value) : List Value :=
  [l5, l6, l7, l8, l9, l10, l11, l12, w13, w14, w15, w16, w17, w18, w19,
    w20, w21, l22, l23, w24, l25, w26, l27]

/-- The locals of absolute `func 17` while the walk runs.  Locals 18, 19,
20, 21 and 26 hold the five hoisted words. -/
@[reducible] def walkLocals (l5 l6 l7 l8 l9 l10 l11 l12 w13 w14 w15 w16 w17
    l22 l23 w24 l25 l27 : Value) (h : SipHash.Hoist) : List Value :=
  rawLocals l5 l6 l7 l8 l9 l10 l11 l12 w13 w14 w15 w16 w17
    (.i64 h.rot0) (.i64 h.mid1) (.i64 h.pre1) (.i64 h.base3) l22 l23 w24
    l25 (.i64 h.base2) l27

set_option maxHeartbeats 2000000 in
/-- The hash of one turn of the walk, WAT 3843 to 3976.  The run leaves the
compiled hash on the operand stack and clobbers locals 14, 15, 16, 17 and
24.  The continuation is universal in those five words, so a caller never
unfolds the flat term. -/
theorem twp_resize_hash [WasmSmallStepGS hlc Universal.State]
    (k0 k1 : UInt64) (key : UInt32) (h : SipHash.Hoist)
    (hh : h = SipHash.hoist k0 k1)
    (p0 p1 p2 p3 p4 : UInt32)
    (l5 l6 l7 l8 l9 l10 l11 l12 w13 w15 w16 w17 l22 l23 w24 l25 l27 :
      Value)
    {values : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    ⊢@{HeapIProp} (iprop%
      ((∀ (a14 a15 a16 a17 a24 : UInt64),
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
              walkLocals l5 l6 l7 l8 l9 l10 l11 l12 w13 (.i64 a14)
                (.i64 a15) (.i64 a16) (.i64 a17) l22 l23 (.i64 a24) l25
                l27 h,
              .i64 (SipHash.hashU32Low k0 k1 key) :: values⟩,
            code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }]) -∗
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
              walkLocals l5 l6 l7 l8 l9 l10 l11 l12 w13
                (.i64 key.toUInt64) w15 w16 w17 l22 l23 w24 l25 l27 h,
              .i64 key.toUInt64 :: values⟩,
            resizeHashPhase code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) := by
  subst hh
  iintro Hcont
  simp only [resizeHashPhase, walkLocals, rawLocals]
  wasm_twp_pures [twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_orI64 twp_xorI64 twp_localGet
    twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_constI64
    twp_xorI64 twp_localGet twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_localGet twp_constI64 twp_rotlI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_addI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_constI64
    twp_rotlI64 twp_localGet twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64 twp_localGet twp_localGet
    twp_constI64 twp_rotlI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_xorI64 twp_constI64 twp_rotlI64 twp_xorI64 twp_localGet
    twp_localGet twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_shrUI64 twp_xorI64 twp_localGet twp_xorI64]
  have hflat : SipHash.hashU32Low k0 k1 key
      = resizeInlineHash (SipHash.hoist k0 k1) key :=
    (resizeInlineHash_eq k0 k1 key).symm
  simp only [resizeInlineHash, resizeCompress, roundWasm1, roundWasm2,
    finalWasm] at hflat
  isimp only [rotlWasm13, rotlWasm16, rotlWasm17, rotlWasm21, rotlWasm32,
    shrU64Wasm32, ← hflat]
  iapply Hcont

/-! ## The old bucket of one turn, WAT 3825 to 3842 -/

/-- Move an owned word between two names of one address. -/
theorem wordMove32 [WasmHeapGS Universal.State]
    {address target word : UInt32} (haddress : target = address) :
    pointsTo_u32 0 address word ⊢ pointsTo_u32 0 target word := by
  rw [haddress]

/-- The lowest flagged byte of the group mask, as `i64.ctz` divided by
eight. -/
theorem ctzByte_of_lowestSetByte {msk : UInt64}
    (hmask : msk &&& Table.REP80 = msk) {j0 : Nat}
    (hlow : Table.lowestSetByte msk = some j0) :
    (UInt64.ofNat (ctz64 64 msk)).toUInt32 >>> 3 = UInt32.ofNat j0 := by
  have hj8 : j0 < 8 :=
    List.mem_range.mp (List.mem_of_find?_eq_some hlow)
  obtain ⟨hbit, hmin⟩ := Table.lowest_bit_of_lowestSetByte hmask hlow
  have hctz : ctz64 64 msk = 8 * j0 + 7 := by
    have := Table.ctz64_eq 64 (Nat.le_refl 64) msk (8 * j0 + 7) (by omega)
      hbit hmin
    omega
  have h32 : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftRight, UInt64.toNat_toUInt32, UInt64.toNat_ofNat',
    hctz, UInt32.toNat_ofNat_of_lt' (by omega),
    show (3 : UInt32).toNat % 32 = 3 from rfl, Nat.shiftRight_eq_div_pow,
    Nat.mod_eq_of_lt (by omega : 8 * j0 + 7 < 2 ^ 64)]
  omega

/-- The bucket that one turn of the walk moves, as the compiled code
computes its address at WAT 3827 to 3839. -/
theorem oldBucketAddr_of_wasm (ctrlOld : UInt32) {off j0 i : Nat}
    (hi : i = off + j0) (_hib : i < 2 ^ 32) :
    (4294967288 : UInt32) +
        (ctrlOld - (UInt32.ofNat off + UInt32.ofNat j0) <<< (3 : UInt32))
      = Table.bucketAddr ctrlOld i := by
  have hsum : UInt32.ofNat off + UInt32.ofNat j0 = UInt32.ofNat i := by
    apply UInt32.toNat_inj.mp
    rw [UInt32.toNat_add, UInt32.toNat_ofNat', UInt32.toNat_ofNat',
      UInt32.toNat_ofNat', hi]
    have h32 : UInt32.size = 4294967296 := rfl
    omega
  rw [hsum, negEightAdd, slotAddr_of_wasm]

set_option maxHeartbeats 2000000 in
/-- WAT 3825 to 3842: the address of the old bucket of this turn and its
key.  The two words that the insert probe reads later, the new control
pointer and the new bucket mask, go on the operand stack first. -/
theorem twp_resize_addr [WasmSmallStepGS hlc Universal.State]
    (msk : UInt64) (j0 b i : Nat) (key : UInt32) (h : SipHash.Hoist)
    (p0 p1 p3 p4 ctrlNew ctrlOld maskNew : UInt32)
    (hmask : msk &&& Table.REP80 = msk)
    (hlow : Table.lowestSetByte msk = some j0)
    (hi : i = 8 * b + j0) (hib : i < 2 ^ 32)
    (hbucketFits : (Table.bucketAddr ctrlOld i).toNat + 4 ≤ UInt32.size)
    (l5 l6 l7 l8 l12 w14 w15 w16 w17 l22 l23 w24 l25 l27 : Value)
    {values : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      pointsTo_u32 0 (Table.bucketAddr ctrlOld i) key ∗
      (pointsTo_u32 0 (Table.bucketAddr ctrlOld i) key -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * b)), .i32 p3,
                .i32 p4],
                walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                  (.i32 maskNew) l12 (.i64 msk) (.i64 key.toUInt64) w15
                  w16 w17 (.i32 (Table.bucketAddr ctrlOld i)) l23 w24 l25
                  l27 h,
                .i64 key.toUInt64 :: .i32 maskNew :: .i32 ctrlNew ::
                  values⟩,
              code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * b)), .i32 p3,
              .i32 p4],
              walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                (.i32 maskNew) l12 (.i64 msk) w14 w15 w16 w17 l22 l23 w24
                l25 l27 h,
              values⟩,
            addrPhase code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hkey, Hcont⟩
  have hfa := offset_facts (Table.bucketAddr ctrlOld i) 0 0 rfl (by omega)
  simp only [addrPhase, walkLocals, rawLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_localGet
    twp_ctzI64 twp_wrapI64 twp_const twp_shrU twp_localGet twp_add
    twp_const twp_shl twp_sub twp_const twp_add]
  isimp only [wrapWasm, shrU32Wasm3, shl32Wasm3,
    ctzByte_of_lowestSetByte hmask hlow,
    oldBucketAddr_of_wasm ctrlOld hi hib]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave Hkey := wordMove32 (UInt32.add_zero (Table.bucketAddr ctrlOld i))
    $$ Hkey
  wasm_twp_rebind Wasm.SmallStep.twp_load32UI64
    (address := Table.bucketAddr ctrlOld i) (offset := 0) key
    hfa.1 hfa.2.1 hfa.2.2.1 hfa.2.2.2 with Hkey
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave Hkey :=
    wordMove32 (UInt32.add_zero (Table.bucketAddr ctrlOld i)).symm $$ Hkey
  iapply Hcont $$ Hkey

/-! ## The probe of a table that the walk is still building

The fresh table of the resize holds its entries before the compiled code
writes the two counters, so `Table.WF` does not hold while the walk runs.
The three lemmas below are the parts of `Project.RustHashMap.ProbeStop`
that the probe needs, with the counters taken out of the hypotheses.  A
short list of entries stands in for `1 <= growth_left`. -/

/-- A window with an `EMPTY` byte, inside the probe fuel. -/
theorem exists_empty_window_weak {K V : Type} {hashf : K → UInt64}
    {t : Table K V} (hw : Table.Layout hashf t)
    (hsp : ∀ i, i < t.buckets → Table.isSpecial (t.ctrlAt i) = true →
      t.ctrlAt i = Table.EMPTY)
    (hlen : (Table.toList t).length < t.buckets) (hsh : UInt64) :
    ∃ N, N < Table.probeFuel t ∧
      Table.matchEmpty (t.window hsh N) = true := by
  obtain ⟨e, he, hemp⟩ := hw.exists_empty_of_lt hsp hlen
  have hne := hw.firstSpecial_probe hsh he hemp
  rcases hf : Table.firstSpecial t hsh (Table.probeFuel t) 0 with _ | ⟨N, j⟩
  · exact absurd hf hne
  obtain ⟨-, hlt, hls, -⟩ := Table.firstSpecial_some t hsh _ _ _ _ hf
  unfold Table.window at hls
  obtain ⟨hj, hspj, -⟩ := Table.lowestSpecial_groupAt_some hls
  refine ⟨N, by omega, ?_⟩
  rw [Table.matchEmpty_window]
  refine ⟨j, hj, ?_⟩
  have hp := hw.probe_lt hsh N
  have hmir := hw.mirror ((Table.probeSeq t hsh N).pos + j) (by omega)
  by_cases hpad : Table.IsPad t.buckets ((Table.probeSeq t hsh N).pos + j)
  · rw [hmir, if_pos hpad]
  · rw [hmir, if_neg hpad]
    rw [hmir, if_neg hpad] at hspj
    exact hsp _ (Nat.mod_lt _ hw.pos) hspj

/-- The first window with an `EMPTY` byte. -/
theorem exists_first_empty_window_weak {K V : Type} {hashf : K → UInt64}
    {t : Table K V} (hw : Table.Layout hashf t)
    (hsp : ∀ i, i < t.buckets → Table.isSpecial (t.ctrlAt i) = true →
      t.ctrlAt i = Table.EMPTY)
    (hlen : (Table.toList t).length < t.buckets) (hsh : UInt64) :
    ∃ N, N < Table.probeFuel t ∧
      Table.matchEmpty (t.window hsh N) = true ∧
      ∀ m, m < N → Table.matchEmpty (t.window hsh m) = false := by
  have hex : ∃ N, Table.matchEmpty (t.window hsh N) = true := by
    obtain ⟨N, -, hN⟩ := exists_empty_window_weak hw hsp hlen hsh
    exact ⟨N, hN⟩
  obtain ⟨N, hN, hmatch⟩ := exists_empty_window_weak hw hsp hlen hsh
  refine ⟨Nat.find hex, Nat.lt_of_le_of_lt (Nat.find_le hmatch) hN,
    Nat.find_spec hex, ?_⟩
  intro m hm
  exact Bool.eq_false_iff.mpr (Nat.find_min hex hm)

/-- With room to insert and at most eight buckets, the first group holds a
special byte, and the lowest one names an `EMPTY` bucket. -/
theorem lowestSpecial_groupAt_zero_weak {K V : Type} {hashf : K → UInt64}
    {t : Table K V} (hw : Table.Layout hashf t)
    (hsp : ∀ i, i < t.buckets → Table.isSpecial (t.ctrlAt i) = true →
      t.ctrlAt i = Table.EMPTY)
    (hlen : (Table.toList t).length < t.buckets) (hb8 : t.buckets ≤ 8) :
    ∃ j0, Table.lowestSpecial (Table.groupAt t 0) = some j0 ∧
      j0 < t.buckets ∧ t.ctrlAt j0 = Table.EMPTY := by
  obtain ⟨e, he, hemp⟩ := hw.exists_empty_of_lt hsp hlen
  have hex : Table.lowestSpecial (Table.groupAt t 0) ≠ none :=
    Table.lowestSpecial_ne_none_of_mem
      (Table.mem_groupAt.2 ⟨e, by omega, rfl⟩)
      (by rw [Nat.zero_add, hemp]; decide)
  rcases hls0 : Table.lowestSpecial (Table.groupAt t 0) with _ | x
  · exact absurd hls0 hex
  · obtain ⟨hx, hsx, hminx⟩ := Table.lowestSpecial_groupAt_some hls0
    have hxe : x ≤ e := by
      by_contra hlt
      have := hminx e (by omega)
      rw [Nat.zero_add, hemp] at this
      cases this
    rw [Nat.zero_add] at hsx
    exact ⟨x, rfl, by omega, hsp _ (by omega) hsx⟩

/-- The candidate of the compiled probe always fixes up to an `EMPTY`
bucket. -/
theorem fixInsertIndex_spec_weak {K V : Type} {hashf : K → UInt64}
    {t : Table K V} (hw : Table.Layout hashf t)
    (hsp : ∀ i, i < t.buckets → Table.isSpecial (t.ctrlAt i) = true →
      t.ctrlAt i = Table.EMPTY)
    (hlen : (Table.toList t).length < t.buckets) {c : Nat}
    (hc : c < t.buckets)
    (hspecial : Table.isSpecial (t.ctrlAt c) = true ∨ t.buckets ≤ 8) :
    Table.fixInsertIndex t c < t.buckets ∧
      t.ctrlAt (Table.fixInsertIndex t c) = Table.EMPTY := by
  unfold Table.fixInsertIndex
  by_cases hfull : Table.isFull (t.ctrlAt c) = true
  · rw [if_pos hfull]
    have hb8 : t.buckets ≤ 8 := by
      rcases hspecial with hs | hs
      · exact absurd hfull (Table.isSpecial_iff.mp hs)
      · exact hs
    obtain ⟨x, hls0, hxb, hxe⟩ :=
      lowestSpecial_groupAt_zero_weak hw hsp hlen hb8
    rw [hls0]
    exact ⟨hxb, hxe⟩
  · rw [if_neg hfull]
    exact ⟨hc, hsp c hc (Table.isSpecial_iff.mpr hfull)⟩

/-! ## The insert probe of one turn, WAT 3977 to 4012 -/

/-- The compiled hash and the model hash have the same low word. -/
theorem toUInt32_hashLow (k0 k1 : UInt64) (key : UInt32) :
    (SipHash.hashU32Low k0 k1 key).toUInt32
      = (SipHash.hashU32 k0 k1 key).toUInt32 := by
  apply UInt32.toNat_inj.mp
  rw [UInt64.toNat_toUInt32, UInt64.toNat_toUInt32]
  exact (Table.h1_hashU32Low k0 k1 key).symm

/-- One group of an owned control range, with a wand that takes it back. -/
theorem groupAt_focus [WasmSmallStepGS hlc Universal.State]
    (ctrl : UInt32) (t : Table UInt32 UInt32) {pos : Nat}
    (hpos : pos + 8 ≤ t.ctrl.length) :
    Slices.ByteSlice (α := Universal.State) 0 ctrl t.ctrl ⊢
      iprop(⌜(ctrl + UInt32.ofNat pos).toNat + 8 < UInt32.size⌝ ∗
        pointsTo_u64 0 (ctrl + UInt32.ofNat pos)
          (Table.groupWord (Table.groupAt t pos)) ∗
        (pointsTo_u64 0 (ctrl + UInt32.ofNat pos)
            (Table.groupWord (Table.groupAt t pos)) -∗
          Slices.ByteSlice 0 ctrl t.ctrl)) := by
  iintro Hctrl
  icases (Table.ByteSlice_groupAt 0 ctrl t hpos).mp $$ Hctrl with
    ⟨Hpre, ⟨%hgb, Hgroup⟩, Hpost⟩
  isplitl_pureexact hgb
  isplitl [Hgroup]
  · iexact Hgroup
  · iintro Hgroup
    iapply (Table.ByteSlice_groupAt 0 ctrl t hpos).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hgroup]
      · isplitl_pureexact hgb
        iexact Hgroup
      · iexact Hpost

/-- The walk of `find_insert_index`: the loop stops at the first window
with a special byte, so the model loop gives the same bucket. -/
theorem findInsertIndexLoop_of_walk {K V : Type} (t : Table K V)
    (hash : UInt64) (N j0 : Nat)
    (hmin : ∀ m, m < N →
      Table.lowestSpecial (Table.groupAt t (Table.probeSeq t hash m).pos)
        = none)
    (hN : Table.lowestSpecial
      (Table.groupAt t (Table.probeSeq t hash N).pos) = some j0) :
    ∀ (fuel k : Nat), k ≤ N → N - k < fuel →
      Table.findInsertIndexLoop t fuel (Table.probeSeq t hash k)
        = some (Table.fixInsertIndex t
            (((Table.probeSeq t hash N).pos + j0) % t.buckets)) := by
  intro fuel
  induction fuel with
  | zero => intro k _ hlt; omega
  | succ f ih =>
    intro k hk hlt
    rcases Nat.eq_or_lt_of_le hk with hkN | hkN
    · subst hkN
      simp only [Table.findInsertIndexLoop, hN]
    · rw [Table.findInsertIndexLoop,
        show Table.lowestSpecial
          (Table.groupAt t (Table.probeSeq t hash k).pos) = none from
          hmin k hkN]
      exact ih (k + 1) hkN (by omega)

/-- `find_insert_index` from the trace of the compiled probe. -/
theorem findInsertIndex_of_walk {K V : Type} (t : Table K V)
    (hash : UInt64) (N j0 : Nat) (hfuel : N < Table.probeFuel t)
    (hmin : ∀ m, m < N →
      Table.lowestSpecial (Table.groupAt t (Table.probeSeq t hash m).pos)
        = none)
    (hN : Table.lowestSpecial
      (Table.groupAt t (Table.probeSeq t hash N).pos) = some j0) :
    Table.findInsertIndex t hash
      = Table.fixInsertIndex t
          (((Table.probeSeq t hash N).pos + j0) % t.buckets) := by
  unfold Table.findInsertIndex
  rw [show Table.probeStart t hash = Table.probeSeq t hash 0 from rfl,
    findInsertIndexLoop_of_walk t hash N j0 hmin hN (Table.probeFuel t) 0
      (by omega) (by omega)]
  rfl

/-- WAT 3977 to 3991: the start position, the first group and the loop. -/
@[reducible] def probePhase (loopBody : Program) : Program :=
  Instruction.wrapI64 :: .localTee 23 :: .and :: .localTee 12 :: .add ::
    .load64 0 :: .constI64 9259542123273814144 :: .andI64 ::
    .localTee 14 :: .constI64 0 :: .neI64 :: .br_if 0 :: .const 8 ::
    .localSet 27 :: [.loop 0 0 loopBody]

/-- WAT 3992 to 4011: one turn of the insert probe. -/
@[reducible] def probeLoopBody : Program :=
  [.localGet 12, .localGet 27, .add, .localSet 12, .localGet 27,
    .const 8, .add, .localSet 27, .localGet 9, .localGet 12,
    .localGet 11, .and, .localTee 12, .add, .load64 0,
    .constI64 9259542123273814144, .andI64, .localTee 14, .eqzI64,
    .br_if 0]

set_option maxRecDepth 1048576 in
/-- The probe is the tail of the block that carries the hash. -/
theorem shape_probe_phase :
    hashTail = probePhase probeLoopBody := by rfl

/-- The frame that `twp_block` makes for the block of WAT 3824 to 4013.
The body stays open, because the shape theorems rewrite it. -/
@[reducible] def hashFrame (body contCode : Program) : ControlFrame :=
  { kind := .block, paramArity := 0, resultArity := 0,
    body := body, continuation := contCode, belowStack := [] }

/-- In a clean table a window with no `EMPTY` byte has no special byte, so
the compiled probe and the model loop stop at the same window. -/
theorem lowestSpecial_none_of_walk {K V : Type} {hashf : K → UInt64}
    {t : Table K V} (hw : Table.Layout hashf t)
    (hsp0 : ∀ i, i < t.buckets → Table.isSpecial (t.ctrlAt i) = true →
      t.ctrlAt i = Table.EMPTY)
    (hsh : UInt64) (k : Nat)
    (hme : Table.matchEmpty (t.window hsh k) = false) :
    Table.lowestSpecial (Table.groupAt t (Table.probeSeq t hsh k).pos)
      = none := by
  rcases hls : Table.lowestSpecial
      (Table.groupAt t (Table.probeSeq t hsh k).pos) with _ | j
  · rfl
  · exfalso
    obtain ⟨hj8, hsp, -⟩ := Table.lowestSpecial_groupAt_some hls
    have hp := hw.probe_lt hsh k
    have hmir := hw.mirror ((Table.probeSeq t hsh k).pos + j) (by omega)
    have hempty : t.ctrlAt ((Table.probeSeq t hsh k).pos + j)
        = Table.EMPTY := by
      by_cases hpad : Table.IsPad t.buckets
          ((Table.probeSeq t hsh k).pos + j)
      · rw [hmir, if_pos hpad]
      · rw [hmir, if_neg hpad]
        rw [hmir, if_neg hpad] at hsp
        exact hsp0 _ (Nat.mod_lt _ hw.pos) hsp
    rw [Bool.eq_false_iff] at hme
    exact hme ((Table.matchEmpty_window t hsh k).mpr ⟨j, hj8, hempty⟩)

/-- A window with an `EMPTY` byte has a lowest special byte. -/
theorem lowestSpecial_some_of_walk {K V : Type} {t : Table K V}
    (hsh : UInt64) (k : Nat)
    (hme : Table.matchEmpty (t.window hsh k) = true) :
    ∃ j0, Table.lowestSpecial
      (Table.groupAt t (Table.probeSeq t hsh k).pos) = some j0 := by
  obtain ⟨j, hj8, hj⟩ := (Table.matchEmpty_window t hsh k).mp hme
  refine Option.ne_none_iff_exists'.mp ?_
  exact Table.lowestSpecial_ne_none_of_mem
    (Table.mem_groupAt.mpr ⟨j, hj8, hj⟩) (by decide)

/-- Every match mask of `match_empty_or_deleted` carries high bits only. -/
theorem specialMask_and_REP80 (g : List UInt8) :
    Table.swarMatchEmptyOrDeleted (Table.groupWord g) &&& Table.REP80
      = Table.swarMatchEmptyOrDeleted (Table.groupWord g) := by
  unfold Table.swarMatchEmptyOrDeleted
  rw [UInt64.and_assoc, UInt64.and_self]

/-- `UInt32.ofNat` of a sum with eight. -/
theorem ofNat_add_eight (a : Nat) :
    UInt32.ofNat (a + 8) = UInt32.ofNat a + 8 := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_add, UInt32.toNat_ofNat',
    show (8 : UInt32).toNat = 8 from rfl]
  omega

set_option maxHeartbeats 4000000 in
/-- The insert probe of one turn of the walk, WAT 3977 to 4012.  The fresh
table is clean and has room, so a window with an `EMPTY` byte exists.  The
loop stops at the first such window.  The exit names the window, the
lowest special byte of it and the match mask, and it ties the bucket to
`Table.findInsertIndex`.  Local 27 holds a different word at the two
exits, so the continuation quantifies over it. -/
theorem twp_resize_probe [WasmSmallStepGS hlc Universal.State]
    {hashf : UInt32 → UInt64} (n : Table UInt32 UInt32) (m : Nat)
    (hm : m ≤ 32) (hbShape : n.buckets = 2 ^ m)
    (hlay : Table.Layout hashf n)
    (hsp : ∀ i, i < n.buckets → Table.isSpecial (n.ctrlAt i) = true →
      n.ctrlAt i = Table.EMPTY)
    (hlen : (Table.toList n).length < n.buckets) (hsh hword : UInt64)
    (hcompat : hword.toUInt32 = hsh.toUInt32) (maskNew : UInt32)
    (hmaskNew : maskNew = UInt32.ofNat (n.buckets - 1))
    (ctrlNew ctrlOld p0 p1 p2 p3 p4 : UInt32) (h : SipHash.Hoist)
    (l5 l6 l7 l8 l12 w13 w14 w15 w16 w17 l22 l23 w24 l25 l27 : Value)
    {body contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    ⊢@{HeapIProp} (iprop%
      (Slices.ByteSlice 0 ctrlNew n.ctrl -∗
      (∀ (pos j0 : Nat) (msk : UInt64) (w27 : Value),
        ⌜msk &&& Table.REP80 = msk ∧
          Table.lowestSetByte msk = some j0 ∧
          (Table.isSpecial
              (Table.ctrlAt n ((pos + j0) % n.buckets)) = true ∨
            n.buckets ≤ 8) ∧
          Table.findInsertIndex n hsh
            = Table.fixInsertIndex n ((pos + j0) % n.buckets)⌝ -∗
        Slices.ByteSlice 0 ctrlNew n.ctrl -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
                walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                  (.i32 maskNew)
                  (.i32 (UInt32.ofNat pos)) w13 (.i64 msk) w15 w16 w17
                  l22 (.i32 hword.toUInt32) w24 l25 w27 h,
                []⟩,
              contCode, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }]) -∗
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
              walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                (.i32 maskNew) l12 w13 w14 w15 w16
                w17 l22 l23 w24 l25 l27 h,
              [.i64 hword, .i32 maskNew,
                .i32 ctrlNew]⟩,
            probePhase probeLoopBody, arity, remainder,
            hashFrame body contCode :: controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) := by
  subst hmaskNew
  iintro Hctrl Hexit
  have hlayout : Table.Layout hashf n := hlay
  have hbpos : 0 < n.buckets := hlayout.pos
  have hclen : n.ctrl.length = n.buckets + 8 := hlayout.ctrl_len
  obtain ⟨N, hNfuel, hNempty, hNmin⟩ :=
    exists_first_empty_window_weak hlay hsp hlen hsh
  obtain ⟨jN, hjN⟩ := lowestSpecial_some_of_walk hsh N hNempty
  have hnone : ∀ k, k < N →
      Table.lowestSpecial (Table.groupAt n (Table.probeSeq n hsh k).pos)
        = none :=
    fun k hk => lowestSpecial_none_of_walk hlayout hsp hsh k (hNmin k hk)
  have hfind : Table.findInsertIndex n hsh
      = Table.fixInsertIndex n
          (((Table.probeSeq n hsh N).pos + jN) % n.buckets) :=
    findInsertIndex_of_walk n hsh N jN hNfuel hnone hjN
  obtain ⟨hjN8, hjNsp, -⟩ := Table.lowestSpecial_groupAt_some hjN
  have hspecial : Table.isSpecial
        (Table.ctrlAt n (((Table.probeSeq n hsh N).pos + jN) % n.buckets))
        = true ∨ n.buckets ≤ 8 := by
    rcases Nat.lt_or_ge n.buckets 8 with hb | hb
    · exact Or.inr (Nat.le_of_lt hb)
    · left
      have hp := hlayout.probe_lt hsh N
      have hmir := hlayout.mirror ((Table.probeSeq n hsh N).pos + jN)
        (by omega)
      rw [if_neg (by unfold Table.IsPad; omega)] at hmir
      rw [← hmir]
      exact hjNsp
  have hlowN : Table.lowestSetByte
      (Table.swarMatchEmptyOrDeleted
        (Table.groupWord (Table.groupAt n (Table.probeSeq n hsh N).pos)))
      = some jN := by
    rw [Table.lowestSetByte_swarMatchEmptyOrDeleted
      (Table.groupAt_length n _)]
    exact hjN
  have hzero : ∀ k, k < N →
      Table.swarMatchEmptyOrDeleted
        (Table.groupWord (Table.groupAt n (Table.probeSeq n hsh k).pos))
        = 0 := by
    intro k hk
    rw [ProbeStop.swarMatchEmptyOrDeleted_eq_zero_iff
      (Table.groupAt_length n _)]
    exact hnone k hk
  have hneN : Table.swarMatchEmptyOrDeleted
      (Table.groupWord (Table.groupAt n (Table.probeSeq n hsh N).pos))
      ≠ 0 := by
    intro hz
    rw [ProbeStop.swarMatchEmptyOrDeleted_eq_zero_iff
      (Table.groupAt_length n _)] at hz
    rw [hz] at hjN
    simp at hjN
  have hprobe : UInt32.ofNat (n.buckets - 1) &&& hword.toUInt32
      = UInt32.ofNat (Table.probeSeq n hsh 0).pos := by
    rw [hcompat, UInt32.and_comm,
      show Table.probeSeq n hsh 0 = Table.probeStart n hsh from rfl,
      ← Table.probeStart_pos_of_wasm n hm hbShape, UInt32.ofNat_toNat]
  have hnext : ∀ k : Nat,
      (UInt32.ofNat (Table.probeSeq n hsh (k + 1)).stride
          + UInt32.ofNat (Table.probeSeq n hsh k).pos)
        &&& UInt32.ofNat (n.buckets - 1)
      = UInt32.ofNat (Table.probeSeq n hsh (k + 1)).pos := by
    intro k
    have hs : (Table.probeSeq n hsh (k + 1)).stride
        = (Table.probeSeq n hsh k).stride + 8 := by
      rw [ProbeStop.probeSeq_stride, ProbeStop.probeSeq_stride]; omega
    rw [hs, ofNat_add_eight, UInt32.add_comm,
      show Table.probeSeq n hsh (k + 1)
        = (Table.probeSeq n hsh k).next n from rfl,
      ← Table.probeNext_pos_of_wasm n hm hbShape
        (Table.probeSeq n hsh k), UInt32.ofNat_toNat]
  have hstrideStep : ∀ k : Nat,
      (8 : UInt32) + UInt32.ofNat (Table.probeSeq n hsh (k + 1)).stride
        = UInt32.ofNat (Table.probeSeq n hsh (k + 1 + 1)).stride := by
    intro k
    have hs : (Table.probeSeq n hsh (k + 1 + 1)).stride
        = (Table.probeSeq n hsh (k + 1)).stride + 8 := by
      rw [ProbeStop.probeSeq_stride, ProbeStop.probeSeq_stride]; omega
    rw [hs, ofNat_add_eight, UInt32.add_comm]
  have haddr : ∀ p : Nat,
      ctrlNew + UInt32.ofNat p = UInt32.ofNat p + ctrlNew + 0 := by
    intro p; rw [UInt32.add_zero, UInt32.add_comm]
  simp only [probePhase, walkLocals, rawLocals]
  wasm_twp_pures [twp_wrapI64]
  isimp only [wrapWasm]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_and]
  isimp only [hprobe]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_add]
  have hp0 : (Table.probeSeq n hsh 0).pos < n.buckets :=
    hlayout.probe_lt hsh 0
  ihave ⟨%hgb0, Hgroup, Hclose⟩ :=
    groupAt_focus ctrlNew n (pos := (Table.probeSeq n hsh 0).pos)
      (by omega) $$ Hctrl
  ihave Hgroup :=
    wordMove64 (haddr (Table.probeSeq n hsh 0).pos).symm $$ Hgroup
  have hgf0 := offset_facts64
    (UInt32.ofNat (Table.probeSeq n hsh 0).pos + ctrlNew) 0 0 rfl
    (by rw [UInt32.add_comm]; omega)
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := UInt32.ofNat (Table.probeSeq n hsh 0).pos + ctrlNew)
    (offset := 0)
    (Table.groupWord (Table.groupAt n (Table.probeSeq n hsh 0).pos))
    hgf0.1 hgf0.2.1 hgf0.2.2.1 hgf0.2.2.2.1 hgf0.2.2.2.2.1
    hgf0.2.2.2.2.2.1 hgf0.2.2.2.2.2.2.1 hgf0.2.2.2.2.2.2.2 with Hgroup
  ihave Hgroup :=
    wordMove64 (haddr (Table.probeSeq n hsh 0).pos) $$ Hgroup
  ihave Hctrl := Hclose $$ Hgroup
  wasm_twp_pures [twp_constI64 twp_andI64]
  isimp only [ProbeStop.swarMatchEmptyOrDeleted_wasm]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64]
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    iapply Wasm.SmallStep.twp_neI64 (result := 1) (by rw [if_pos hneN])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave Hgo := Hexit $$ %((Table.probeSeq n hsh 0).pos) %jN
      %(Table.swarMatchEmptyOrDeleted (Table.groupWord
          (Table.groupAt n (Table.probeSeq n hsh 0).pos)))
      %l27 %(⟨specialMask_and_REP80 _, hlowN, hspecial, hfind⟩)
    iapply Hgo $$ Hctrl
  · have hz0 := hzero 0 hNpos
    iapply Wasm.SmallStep.twp_neI64 (result := 0)
      (by rw [if_neg (fun hne => hne hz0)])
    iapply Wasm.SmallStep.twp_brIfZero
    isimp only [hz0]
    wasm_twp_pures [twp_const]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := Nat)
      (measure := fun k => N - k)
      (locals := fun k =>
        { params := [.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
          locals := walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
            (.i32 (UInt32.ofNat (n.buckets - 1)))
            (.i32 (UInt32.ofNat (Table.probeSeq n hsh k).pos)) w13
            (.i64 0) w15 w16 w17 l22 (.i32 hword.toUInt32) w24 l25
            (.i32 (UInt32.ofNat (Table.probeSeq n hsh (k + 1)).stride)) h,
          values := [] })
      (I := fun k => iprop(
        ⌜k < N⌝ ∗
        Slices.ByteSlice 0 ctrlNew n.ctrl ∗
        (∀ (pos j0 : Nat) (msk : UInt64) (w27 : Value),
          ⌜msk &&& Table.REP80 = msk ∧
            Table.lowestSetByte msk = some j0 ∧
            (Table.isSpecial
                (Table.ctrlAt n ((pos + j0) % n.buckets)) = true ∨
              n.buckets ≤ 8) ∧
            Table.findInsertIndex n hsh
              = Table.fixInsertIndex n ((pos + j0) % n.buckets)⌝ -∗
          Slices.ByteSlice 0 ctrlNew n.ctrl -∗
          WP (.running
              ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
                  walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                    (.i32 (UInt32.ofNat (n.buckets - 1)))
                    (.i32 (UInt32.ofNat pos)) w13 (.i64 msk) w15 w16 w17
                    l22 (.i32 hword.toUInt32) w24 l25 w27 h,
                  []⟩,
                contCode, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }])))
      (initial := 0)
      (initialLocals := _)
    · rfl
    · rfl
    · intro k
      iintro Hrec ⟨%hkN, Hctrl, Hexit⟩
      simp only [Wasm.SmallStep.loopBodyExpr]
      simp only [probeLoopBody, walkLocals, rawLocals]
      wasm_twp_pures [twp_localGet twp_localGet twp_add]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      isimp only [hstrideStep k]
      wasm_twp_pures [twp_localGet twp_localGet twp_localGet twp_and]
      isimp only [hnext k]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_add]
      have hpk : (Table.probeSeq n hsh (k + 1)).pos < n.buckets :=
        hlayout.probe_lt hsh (k + 1)
      ihave ⟨%hgbk, Hgroup, Hclose⟩ :=
        groupAt_focus ctrlNew n (pos := (Table.probeSeq n hsh (k + 1)).pos)
          (by omega) $$ Hctrl
      ihave Hgroup :=
        wordMove64 (haddr (Table.probeSeq n hsh (k + 1)).pos).symm
          $$ Hgroup
      have hgfk := offset_facts64
        (UInt32.ofNat (Table.probeSeq n hsh (k + 1)).pos + ctrlNew) 0 0
        rfl (by rw [UInt32.add_comm]; omega)
      wasm_twp_rebind Wasm.SmallStep.twp_load64
        (address :=
          UInt32.ofNat (Table.probeSeq n hsh (k + 1)).pos + ctrlNew)
        (offset := 0)
        (Table.groupWord
          (Table.groupAt n (Table.probeSeq n hsh (k + 1)).pos))
        hgfk.1 hgfk.2.1 hgfk.2.2.1 hgfk.2.2.2.1 hgfk.2.2.2.2.1
        hgfk.2.2.2.2.2.1 hgfk.2.2.2.2.2.2.1 hgfk.2.2.2.2.2.2.2
        with Hgroup
      ihave Hgroup :=
        wordMove64 (haddr (Table.probeSeq n hsh (k + 1)).pos) $$ Hgroup
      ihave Hctrl := Hclose $$ Hgroup
      wasm_twp_pures [twp_constI64 twp_andI64]
      isimp only [ProbeStop.swarMatchEmptyOrDeleted_wasm]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      rcases Nat.lt_or_ge (k + 1) N with hlt | hge
      · have hzk := hzero (k + 1) hlt
        iapply Wasm.SmallStep.twp_eqzI64 (result := 1)
          (by rw [if_pos hzk])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        isimp only [hzk]
        ihave Hback := Hrec $$ %(k + 1)
          %(by omega : N - (k + 1) < N - k)
        iapply Hback
        isplitl_pureexact hlt
        iframe Hctrl Hexit
      · have hkN1 : k + 1 = N := by omega
        subst hkN1
        iapply Wasm.SmallStep.twp_eqzI64 (result := 0)
          (by rw [if_neg hneN])
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_exitControl (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        iapply Wasm.SmallStep.twp_exitControl (by rfl)
        simp only [List.take_zero, List.nil_append]
        ihave Hgo := Hexit $$ %((Table.probeSeq n hsh (k + 1)).pos) %jN
          %(Table.swarMatchEmptyOrDeleted (Table.groupWord
              (Table.groupAt n (Table.probeSeq n hsh (k + 1)).pos)))
          %(Value.i32
            (UInt32.ofNat (Table.probeSeq n hsh (k + 1 + 1)).stride))
          %(⟨specialMask_and_REP80 _, hlowN, hspecial, hfind⟩)
        iapply Hgo $$ Hctrl
    · isplitl_pureexact hNpos
      iframe Hctrl Hexit

/-! ## The group advance of one turn, WAT 3797 to 3823 -/

/-- WAT 3798 to 3801 and 3819 to 3822: the guard of the group advance and
the turn of the special mask into the full mask. -/
@[reducible] def advPhase (loopBody : Program) : Program :=
  Instruction.localGet 13 :: .constI64 0 :: .neI64 :: .br_if 0 ::
    .loop 0 0 loopBody :: .localGet 13 ::
    .constI64 9259542123273814144 :: .xorI64 :: [.localSet 13]

/-- WAT 3802 to 3818: one turn of the group advance. -/
@[reducible] def advLoopBody : Program :=
  [.localGet 2, .const 8, .add, .localSet 2, .localGet 4, .const 8,
    .add, .localTee 4, .load64 0, .constI64 9259542123273814144,
    .andI64, .localTee 13, .constI64 9259542123273814144, .eqI64,
    .br_if 0]

set_option maxRecDepth 1048576 in
/-- The group advance is the block at index 0 of the walk body. -/
theorem shape_adv_body : advBody = advPhase advLoopBody := by rfl

/-- The `xor` of WAT 3819 to 3822 turns the special mask of a group into
its full mask. -/
theorem specialMask_xor (g : UInt64) :
    (g &&& (9259542123273814144 : UInt64)) ^^^ 9259542123273814144
      = Table.swarMatchFull g := by
  rw [show (9259542123273814144 : UInt64) = Table.REP80 from rfl,
    ResizePures.and_xor_self]
  rfl

/-- Every full mask carries high bits only. -/
theorem swarMatchFull_and_REP80 (g : UInt64) :
    Table.swarMatchFull g &&& Table.REP80 = Table.swarMatchFull g := by
  unfold Table.swarMatchFull
  rw [UInt64.and_assoc, UInt64.and_self]

/-- A group index below the group count of the walk names eight control
bytes of the live range.  The first group is the only one a table with
fewer than eight buckets has. -/
theorem walkGroups_load_bound {K V : Type} {hashf : K → UInt64}
    {t : Table K V} (hw : Table.Layout hashf t) {c : Nat} (hc1 : 1 ≤ c)
    (hc : c < ResizePures.walkGroups t) : 8 * c + 8 ≤ t.buckets := by
  unfold ResizePures.walkGroups at hc
  by_cases hsmall : t.buckets < 8
  · rw [if_pos hsmall] at hc; omega
  · rw [if_neg hsmall] at hc
    obtain ⟨m, hm, hm1, hpow⟩ := hw.shape
    have hdvd : 8 ∣ t.buckets := by
      have hm3 : 3 ≤ m := by
        by_contra hlt
        interval_cases m <;> omega
      rw [hpow, show m = 3 + (m - 3) by omega, Nat.pow_add]
      exact Dvd.intro _ rfl
    obtain ⟨q, hq⟩ := hdvd
    rw [hq] at hc ⊢
    rw [Nat.mul_div_cancel_left _ (by omega)] at hc
    omega

/-- A group index at or above the group count leaves no work. -/
theorem walkFrom_nil_of_ge {K V : Type} (t : Table K V) {N c : Nat}
    (hc : N ≤ c) : ResizePures.walkFrom t N c = [] := by
  unfold ResizePures.walkFrom
  rw [List.drop_eq_nil_of_le (by rw [List.length_range]; omega)]
  rfl

/-- The first group at or after `c` that still holds a full bucket.  The
group advance of WAT 3802 to 3818 walks to it. -/
theorem walkFrom_first {K V : Type} (t : Table K V) (N : Nat) :
    ∀ (r c : Nat), N ≤ c + r → ResizePures.walkFrom t N c ≠ [] →
      ∃ c', c ≤ c' ∧ c' < N ∧
        Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * c'))) ≠ 0 ∧
        ResizePures.walkFrom t N c' = ResizePures.walkFrom t N c ∧
        ∀ d, c ≤ d → d < c' →
          Table.swarMatchFull
            (Table.groupWord (Table.groupAt t (8 * d))) = 0 := by
  intro r
  induction r with
  | zero =>
    intro c hle hne
    exact absurd (walkFrom_nil_of_ge t (by omega)) hne
  | succ r ih =>
    intro c hle hne
    rcases Nat.lt_or_ge c N with hc | hc
    · by_cases hz : Table.swarMatchFull
          (Table.groupWord (Table.groupAt t (8 * c))) = 0
      · have hskip := ResizePures.walkFrom_skip t hc hz
        obtain ⟨c', hc1, hc2, hc3, hc4, hc5⟩ :=
          ih (c + 1) (by omega) (by rw [← hskip]; exact hne)
        refine ⟨c', by omega, hc2, hc3, by rw [hc4, hskip], ?_⟩
        intro d hd1 hd2
        rcases Nat.eq_or_lt_of_le hd1 with hde | hdl
        · rw [← hde]; exact hz
        · exact hc5 d (by omega) hd2
      · exact ⟨c, Nat.le_refl c, hc, hz, rfl, fun d hd1 hd2 => by omega⟩
    · exact absurd (walkFrom_nil_of_ge t hc) hne

set_option maxHeartbeats 4000000 in
/-- The group advance of one turn, WAT 3797 to 3823.  The block keeps the
mask of the current group when it still flags a bucket.  Otherwise the
loop walks to the next group with a full bucket and builds its full mask.
The walk always has work left, so such a group exists. -/
theorem twp_resize_adv [WasmSmallStepGS hlc Universal.State]
    {hashf : UInt32 → UInt64} (t : Table UInt32 UInt32)
    (hlayout : Table.Layout hashf t) (ctrlOld : UInt32) (b : Nat)
    (msk : UInt64) (hmask : msk &&& Table.REP80 = msk)
    (hb : b < ResizePures.walkGroups t)
    (hwork : ResizePures.walkRem t (ResizePures.walkGroups t) b msk ≠ [])
    (p0 p1 p3 : UInt32) (h : SipHash.Hoist)
    (l5 l6 l7 l8 l9 l10 l11 l12 w14 w15 w16 w17 l22 l23 w24 l25 l27 :
      Value)
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    ⊢@{HeapIProp} (iprop%
      (Slices.ByteSlice 0 ctrlOld t.ctrl -∗
      (∀ (b' : Nat) (msk' : UInt64),
        ⌜b ≤ b' ∧ b' < ResizePures.walkGroups t ∧ msk' ≠ 0 ∧
          msk' &&& Table.REP80 = msk' ∧
          ResizePures.walkRem t (ResizePures.walkGroups t) b' msk'
            = ResizePures.walkRem t (ResizePures.walkGroups t) b msk⌝ -∗
        Slices.ByteSlice 0 ctrlOld t.ctrl -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * b')), .i32 p3,
                .i32 (ctrlOld + UInt32.ofNat (8 * b'))],
                walkLocals l5 l6 l7 l8 l9 l10 l11 l12 (.i64 msk') w14
                  w15 w16 w17 l22 l23 w24 l25 l27 h,
                []⟩,
              contCode, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }]) -∗
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * b)), .i32 p3,
              .i32 (ctrlOld + UInt32.ofNat (8 * b))],
              walkLocals l5 l6 l7 l8 l9 l10 l11 l12 (.i64 msk) w14 w15
                w16 w17 l22 l23 w24 l25 l27 h,
              []⟩,
            Instruction.block 0 0 advBody :: contCode, arity, remainder,
            controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) := by
  iintro Hctrl Hexit
  have hclen : t.ctrl.length = t.buckets + 8 := hlayout.ctrl_len
  have hoff : ∀ d : Nat,
      (8 : UInt32) + UInt32.ofNat (8 * d) = UInt32.ofNat (8 * (d + 1)) := by
    intro d
    rw [show 8 * (d + 1) = 8 * d + 8 by omega, ofNat_add_eight,
      UInt32.add_comm]
  have haddr4 : ∀ d : Nat,
      (8 : UInt32) + (ctrlOld + UInt32.ofNat (8 * d))
        = ctrlOld + UInt32.ofNat (8 * (d + 1)) := by
    intro d
    rw [← UInt32.add_assoc, UInt32.add_comm (8 : UInt32) ctrlOld,
      UInt32.add_assoc, hoff d]
  iapply Wasm.SmallStep.twp_block
  simp only [shape_adv_body, advPhase, walkLocals, rawLocals]
  wasm_twp_pures [twp_localGet twp_constI64]
  by_cases hz : msk = 0
  · subst hz
    have hwf0 : ResizePures.walkFrom t (ResizePures.walkGroups t) (b + 1)
        ≠ [] := by
      rw [← ResizePures.walkRem_zero t (ResizePures.walkGroups t) b]
      exact hwork
    obtain ⟨c, hc1, hc2, hc3, hc4, hc5⟩ :=
      walkFrom_first t (ResizePures.walkGroups t)
        (ResizePures.walkGroups t) (b + 1) (by omega) hwf0
    iapply Wasm.SmallStep.twp_neI64 (result := 0)
      (by rw [if_neg (fun hne => hne rfl)])
    iapply Wasm.SmallStep.twp_brIfZero
    iapply Wasm.SmallStep.twp_loop_wf_family
      (ι := Nat × Value)
      (measure := fun i => c - i.1)
      (locals := fun i =>
        { params := [.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * i.1)),
            .i32 p3, .i32 (ctrlOld + UInt32.ofNat (8 * i.1))],
          locals := walkLocals l5 l6 l7 l8 l9 l10 l11 l12 i.2 w14 w15
            w16 w17 l22 l23 w24 l25 l27 h,
          values := [] })
      (I := fun i => iprop(
        ⌜b ≤ i.1 ∧ i.1 < c⌝ ∗
        Slices.ByteSlice 0 ctrlOld t.ctrl ∗
        (∀ (b' : Nat) (msk' : UInt64),
          ⌜b ≤ b' ∧ b' < ResizePures.walkGroups t ∧ msk' ≠ 0 ∧
            msk' &&& Table.REP80 = msk' ∧
            ResizePures.walkRem t (ResizePures.walkGroups t) b' msk'
              = ResizePures.walkRem t (ResizePures.walkGroups t) b 0⌝ -∗
          Slices.ByteSlice 0 ctrlOld t.ctrl -∗
          WP (.running
              ⟨⟨[.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * b')),
                  .i32 p3, .i32 (ctrlOld + UInt32.ofNat (8 * b'))],
                  walkLocals l5 l6 l7 l8 l9 l10 l11 l12 (.i64 msk') w14
                    w15 w16 w17 l22 l23 w24 l25 l27 h,
                  []⟩,
                contCode, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }])))
      (initial := (b, Value.i64 0))
      (initialLocals := _) (belowStack := ([] : List Value))
    · rfl
    · rfl
    · intro i
      iintro Hrec ⟨%hdd, Hctrl, Hexit⟩
      obtain ⟨hdb, hd⟩ := hdd
      simp only [Wasm.SmallStep.loopBodyExpr]
      simp only [advLoopBody, walkLocals, rawLocals]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_localGet twp_const twp_add]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      isimp only [hoff i.1, haddr4 i.1]
      have hgb := walkGroups_load_bound hlayout (c := i.1 + 1)
        (by omega) (by omega)
      ihave ⟨%hgbk, Hgroup, Hclose⟩ :=
        groupAt_focus ctrlOld t (pos := 8 * (i.1 + 1)) (by omega)
          $$ Hctrl
      ihave Hgroup :=
        wordMove64 (UInt32.add_zero
          (ctrlOld + UInt32.ofNat (8 * (i.1 + 1)))) $$ Hgroup
      have hgfk := offset_facts64
        (ctrlOld + UInt32.ofNat (8 * (i.1 + 1))) 0 0 rfl (by omega)
      wasm_twp_rebind Wasm.SmallStep.twp_load64
        (address := ctrlOld + UInt32.ofNat (8 * (i.1 + 1)))
        (offset := 0)
        (Table.groupWord (Table.groupAt t (8 * (i.1 + 1))))
        hgfk.1 hgfk.2.1 hgfk.2.2.1 hgfk.2.2.2.1 hgfk.2.2.2.2.1
        hgfk.2.2.2.2.2.1 hgfk.2.2.2.2.2.2.1 hgfk.2.2.2.2.2.2.2
        with Hgroup
      ihave Hgroup :=
        wordMove64 (UInt32.add_zero
          (ctrlOld + UInt32.ofNat (8 * (i.1 + 1)))).symm $$ Hgroup
      ihave Hctrl := Hclose $$ Hgroup
      wasm_twp_pures [twp_constI64 twp_andI64]
      wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      wasm_twp_pures [twp_constI64]
      rcases Nat.lt_or_ge (i.1 + 1) c with hlt | hge
      · have heq : Table.groupWord (Table.groupAt t (8 * (i.1 + 1)))
            &&& (9259542123273814144 : UInt64) = 9259542123273814144 := by
          rw [show (9259542123273814144 : UInt64) = Table.REP80 from rfl,
            ← ResizePures.swarMatchFull_eq_zero_iff]
          exact hc5 (i.1 + 1) (by omega) hlt
        iapply Wasm.SmallStep.twp_eqI64 (result := 1) (by rw [if_pos heq])
        iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0)
          (by rfl)
        simp only [List.take_zero, List.nil_append]
        ihave Hback := Hrec
          $$ %((i.1 + 1, Value.i64 (Table.groupWord
              (Table.groupAt t (8 * (i.1 + 1)))
                &&& 9259542123273814144)) : Nat × Value)
          %(by omega : c - (i.1 + 1) < c - i.1)
        ieval (dsimp only) at Hback
        iapply Hback
        isplitl_pureexact ⟨by omega, hlt⟩
        iframe Hctrl Hexit
      · have hcEq : i.1 + 1 = c := by omega
        subst hcEq
        have hne : ¬ (Table.groupWord (Table.groupAt t (8 * (i.1 + 1)))
            &&& (9259542123273814144 : UInt64) = 9259542123273814144) := by
          intro heq
          rw [show (9259542123273814144 : UInt64) = Table.REP80 from rfl,
            ← ResizePures.swarMatchFull_eq_zero_iff] at heq
          exact hc3 heq
        iapply Wasm.SmallStep.twp_eqI64 (result := 0)
          (by rw [if_neg hne])
        iapply Wasm.SmallStep.twp_brIfZero
        iapply Wasm.SmallStep.twp_exitControl (by rfl)
        simp only [List.take_zero, List.nil_append]
        wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64]
        isimp only [specialMask_xor]
        wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub]
        iapply Wasm.SmallStep.twp_exitControl (by rfl)
        simp only [List.take_zero, List.drop_zero, List.nil_append]
        ihave Hgo := Hexit $$ %(i.1 + 1)
          %(Table.swarMatchFull
              (Table.groupWord (Table.groupAt t (8 * (i.1 + 1)))))
          %(⟨by omega, hc2, hc3, swarMatchFull_and_REP80 _, by
              rw [ResizePures.walkRem_full t hc2, hc4,
                ResizePures.walkRem_zero]⟩)
        iapply Hgo $$ Hctrl
    · isplitl_pureexact ⟨Nat.le_refl b, by omega⟩
      iframe Hctrl Hexit
  · iapply Wasm.SmallStep.twp_neI64 (result := 1) (by rw [if_pos hz])
    iapply Wasm.SmallStep.twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    ihave Hgo := Hexit $$ %b %msk
      %(⟨Nat.le_refl b, hb, hz, hmask, rfl⟩)
    iapply Hgo $$ Hctrl

/-! ## The mirror fix of one turn, WAT 4019 to 4043 -/

set_option maxRecDepth 1048576 in
/-- The fix block of the walk loop is the block at index 6 of the body. -/
theorem shape_fix_body :
    fixBody =
      [.localGet 9, .localGet 14, .ctzI64, .wrapI64, .const 3, .shrU,
        .localGet 12, .add, .localGet 11, .and, .localTee 12, .add,
        .load8S 0, .const 0, .ltS, .br_if 0, .localGet 9, .load64 0,
        .constI64 9259542123273814144, .andI64, .ctzI64, .wrapI64,
        .const 3, .shrU, .localSet 12] := by rfl

set_option maxHeartbeats 2000000 in
/-- `fix_insert_index` of the walk, WAT 4018 to 4044.  The block turns the
match mask of the insert probe into a bucket, and keeps that bucket when
its control byte is special.  Otherwise it takes the lowest special byte of
the first group.  The answer is `Table.findInsertIndex` once the caller
reads the candidate off `Table.Layout.findInsertIndex_spec`. -/
theorem twp_resize_fix [WasmSmallStepGS hlc Universal.State]
    {hashf : UInt32 → UInt64} (n : Table UInt32 UInt32) (m : Nat)
    (hm : m ≤ 32) (hbShape : n.buckets = 2 ^ m)
    (hlay : Table.Layout hashf n)
    (hclean : ∀ i, i < n.buckets → Table.isSpecial (n.ctrlAt i) = true →
      n.ctrlAt i = Table.EMPTY)
    (hlen : (Table.toList n).length < n.buckets)
    (msk : UInt64) (pos j0 c : Nat)
    (hmask : msk &&& Table.REP80 = msk)
    (hlow : Table.lowestSetByte msk = some j0)
    (hc : c = (pos + j0) % n.buckets)
    (hspecial : Table.isSpecial (n.ctrlAt c) = true ∨ n.buckets ≤ 8)
    (maskNew : UInt32)
    (hmaskNew : maskNew = UInt32.ofNat (n.buckets - 1))
    (ctrlNew ctrlOld p0 p1 p2 p3 p4 : UInt32) (h : SipHash.Hoist)
    (l5 l6 l7 l8 w13 w15 w16 w17 l22 l23 w24 l25 l27 : Value)
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      Slices.ByteSlice 0 ctrlNew n.ctrl ∗
      (Slices.ByteSlice 0 ctrlNew n.ctrl -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
                walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                  (.i32 maskNew)
                  (.i32 (UInt32.ofNat (Table.fixInsertIndex n c))) w13
                  (.i64 msk) w15 w16 w17 l22 l23 w24 l25 l27 h,
                []⟩,
              contCode, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 p3, .i32 p4],
              walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                (.i32 maskNew)
                (.i32 (UInt32.ofNat pos)) w13 (.i64 msk) w15 w16 w17
                l22 l23 w24 l25 l27 h,
              []⟩,
            Instruction.block 0 0 fixBody :: contCode, arity, remainder,
            controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  subst hmaskNew
  iintro ⟨Hctrl, Hexit⟩
  have hlayout : Table.Layout hashf n := hlay
  have hclen : n.ctrl.length = n.buckets + 8 := hlayout.ctrl_len
  have hbpos : 0 < n.buckets := hlayout.pos
  have hcb : c < n.buckets := by rw [hc]; exact Nat.mod_lt _ hbpos
  have hcLt : c < n.ctrl.length := by omega
  have hidx := Table.matchIndex_of_wasm n hm hbShape hmask hlow pos
  have hidxEq : (UInt32.ofNat pos +
      (UInt64.ofNat (ctz64 64 msk)).toUInt32 >>> 3) &&&
      UInt32.ofNat (n.buckets - 1) = UInt32.ofNat c := by
    rw [UInt32.add_comm, hc, ← hidx, UInt32.ofNat_toNat]
  iapply Wasm.SmallStep.twp_block
  simp only [shape_fix_body, walkLocals, rawLocals]
  wasm_twp_pures [twp_localGet twp_localGet twp_ctzI64 twp_wrapI64
    twp_const twp_shrU twp_localGet twp_add twp_localGet twp_and]
  isimp only [wrapWasm, shrU32Wasm3, hidxEq]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_add]
    rewriting [UInt32.add_comm (UInt32.ofNat c) ctrlNew]
  ihave ⟨Hbyte, Hclose⟩ :=
    Func15Insert.ctrlByte_focus ctrlNew n hcLt $$ Hctrl
  wasm_twp_rebind twp_load8S_addr_gen (Table.ctrlAt n c) with Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  wasm_twp_pures [twp_const]
  by_cases hsp : Table.isSpecial (Table.ctrlAt n c) = true
  · have hlt := (ProbeStop.ltS_signByte (Table.ctrlAt n c)).mpr hsp
    iapply Wasm.SmallStep.twp_ltS (result := 1) (by rw [if_pos hlt])
    iapply Wasm.SmallStep.twp_brIf (targetCode := contCode)
      (targetControl := controls) (targetValues := ([] : List Value))
      (by decide : (1 : UInt32) ≠ 0) (by rfl)
    have hfix : Table.fixInsertIndex n c = c := by
      unfold Table.fixInsertIndex
      rw [if_neg (Table.isSpecial_iff.mp hsp)]
    rw [hfix]
    iapply Hexit $$ Hctrl
  · have hfull : Table.isFull (Table.ctrlAt n c) = true := by
      by_contra hf
      exact hsp (Table.isSpecial_iff.mpr hf)
    have hb8 : n.buckets ≤ 8 := by
      rcases hspecial with hs | hs
      · exact absurd hs hsp
      · exact hs
    have hltFalse :
        ¬ ((Int32.ofInt
              (signExtend (Table.ctrlAt n c).toNat 8)).toUInt32.toInt32
            < (0 : UInt32).toInt32) := fun hlt =>
      hsp ((ProbeStop.ltS_signByte _).mp hlt)
    iapply Wasm.SmallStep.twp_ltS (result := 0) (by rw [if_neg hltFalse])
    iapply Wasm.SmallStep.twp_brIfZero
    obtain ⟨jz, hls0, hjzb, hjze⟩ :=
      lowestSpecial_groupAt_zero_weak hlay hclean hlen hb8
    have hfix : Table.fixInsertIndex n c = jz := by
      unfold Table.fixInsertIndex
      rw [if_pos hfull, hls0, Option.getD_some]
    have hmask0 : Table.swarMatchEmptyOrDeleted
          (Table.groupWord (Table.groupAt n 0)) &&& Table.REP80
        = Table.swarMatchEmptyOrDeleted
            (Table.groupWord (Table.groupAt n 0)) := by
      unfold Table.swarMatchEmptyOrDeleted
      rw [UInt64.and_assoc, UInt64.and_self]
    have hlow0 : Table.lowestSetByte
        (Table.swarMatchEmptyOrDeleted
          (Table.groupWord (Table.groupAt n 0))) = some jz := by
      rw [Table.lowestSetByte_swarMatchEmptyOrDeleted
        (Table.groupAt_length n 0), hls0]
    wasm_twp_pures [twp_localGet]
    ihave ⟨%hgb, Hgroup, Hclose⟩ :=
      Func15Insert.group0_focus ctrlNew n (by omega) $$ Hctrl
    have hgf := offset_facts64 ctrlNew 0 0 rfl (by
      have hz : (ctrlNew + 0) = ctrlNew := UInt32.add_zero ctrlNew
      omega)
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := ctrlNew)
      (offset := 0) (Table.groupWord (Table.groupAt n 0))
      hgf.1 hgf.2.1 hgf.2.2.1 hgf.2.2.2.1 hgf.2.2.2.2.1
      hgf.2.2.2.2.2.1 hgf.2.2.2.2.2.2.1 hgf.2.2.2.2.2.2.2 with Hgroup
    ihave Hctrl := Hclose $$ Hgroup
    wasm_twp_pures [twp_constI64 twp_andI64 twp_ctzI64 twp_wrapI64
      twp_const twp_shrU]
    isimp only [ProbeStop.swarMatchEmptyOrDeleted_wasm, wrapWasm,
      shrU32Wasm3, ProbeStop.ctzByte_of_wasm hmask0 hlow0]
    wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    iapply Wasm.SmallStep.twp_exitControl (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    rw [hfix]
    iapply Hexit $$ Hctrl

/-! ## The writes of one turn, WAT 4045 to 4081 -/

/-- The control byte that WAT 4055 to 4060 stores.  The compiled code
shifts the low word of the hash right by 25 and keeps no mask, because
that shift leaves seven bits. -/
theorem tagByte_of_low (y : UInt64) :
    (y.toUInt32 >>> 25).toUInt8 = Table.h2 y := by
  unfold Table.h2
  apply UInt8.toNat_inj.mp
  rw [UInt32.toNat_toUInt8, UInt64.toNat_toUInt8, UInt32.toNat_shiftRight,
    UInt64.toNat_and, UInt64.toNat_shiftRight, UInt64.toNat_toUInt32,
    show UInt32.toNat 25 % 32 = 25 from rfl,
    show UInt64.toNat 25 % 64 = 25 from rfl,
    show UInt64.toNat 127 = 2 ^ 7 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow,
    Nat.shiftRight_eq_div_pow,
    show (2 : Nat) ^ 32 = 2 ^ 25 * 2 ^ 7 from rfl,
    Nat.mod_mul_right_div_self]

/-- `i32.shr_u` at 25. -/
theorem shrU32Wasm25 (x : UInt32) : x >>> ((25 : UInt32) % 32) = x >>> 25 :=
  rfl

/-- The counter step of WAT 4078 to 4080. -/
theorem negOneAdd (x : UInt32) : 4294967295 + x = x - 1 := by
  apply UInt32.toNat_inj.mp
  have hx := UInt32.toNat_lt x
  simp only [UInt32.toNat_add, UInt32.toNat_sub,
    show (4294967295 : UInt32).toNat = 4294967295 from rfl,
    show (1 : UInt32).toNat = 1 from rfl] at *

/-- The control bytes of `Table.place`. -/
theorem place_ctrl (n : Table UInt32 UInt32) (idx : Nat) (tag : UInt8)
    (kv : UInt32 × UInt32) :
    (Table.place n idx tag kv).ctrl
      = (n.ctrl.set idx tag).set (Table.index2 n.buckets idx) tag := rfl

/-- The buckets of `Table.place`. -/
theorem place_slots (n : Table UInt32 UInt32) (idx : Nat) (tag : UInt8)
    (kv : UInt32 × UInt32) :
    (Table.place n idx tag kv).slots = n.slots.set idx (some kv) := rfl

/-- WAT 4045 to 4081: the mask step, the tag byte at the insert index and
at its mirror, the eight-byte move of the old bucket, and the counter. -/
@[reducible] def writePhase (contCode : Program) : Program :=
    Instruction.localGet 15 :: .localGet 13 :: .andI64 :: .localSet 13 ::
    .localGet 9 :: .localGet 12 :: .add :: .localGet 23 :: .const 25 ::
    .shrU :: .localTee 23 :: .store8 0 :: .localGet 9 :: .localGet 12 ::
    .const 4294967288 :: .add :: .localGet 11 :: .and :: .add :: .const 8 ::
    .add :: .localGet 23 :: .store8 0 :: .localGet 9 :: .localGet 12 ::
    .const 3 :: .shl :: .sub :: .const 4294967288 :: .add :: .localGet 22 ::
    .load64 0 :: .store64 0 :: .localGet 3 :: .const 4294967295 :: .add ::
    .localTee 3 :: contCode

/-- The writes and the back edge of one turn. -/
def walkTail : Program := walkBody.drop 7

set_option maxRecDepth 1048576 in
/-- The writes and the back edge are the tail of the walk loop. -/
theorem shape_write_phase :
    walkTail = writePhase [.br_if 0] := by rfl

set_option maxRecDepth 1048576 in
/-- The six parts of one turn of the walk. -/
theorem shape_walk_turn :
    walkBody = .block 0 0 advBody :: .block 0 0 hashBody ::
      .localGet 13 :: .constI64 18446744073709551615 :: .addI64 ::
      .localSet 15 :: .block 0 0 fixBody :: walkTail := by rfl

set_option maxHeartbeats 4000000 in
/-- The writes of one turn of the walk, WAT 4045 to 4081.  The fresh table
takes the tag at `idx` and at its mirror, and the eight bytes of the old
bucket.  That is `Table.place`.  The old bucket is read only. -/
theorem twp_resize_write [WasmSmallStepGS hlc Universal.State]
    {hashf : UInt32 → UInt64} (n : Table UInt32 UInt32)
    (hlayout : Table.Layout hashf n) (m : Nat) (hm : m ≤ 32)
    (hbShape : n.buckets = 2 ^ m)
    (idx i : Nat) (hidx : idx < n.buckets)
    (hempty : n.ctrlAt idx = Table.EMPTY)
    (tag : UInt8) (hashWord : UInt32)
    (htag : (hashWord >>> 25).toUInt8 = tag)
    (key value ctrlNew ctrlOld counter maskNew : UInt32)
    (hmaskNew : maskNew = UInt32.ofNat (n.buckets - 1))
    (msk mskPred : UInt64)
    (hroom : 8 * n.buckets ≤ ctrlNew.toNat)
    (holdFits : (Table.bucketAddr ctrlOld i).toNat + 8 ≤ UInt32.size)
    (p0 p1 p2 p4 : UInt32) (h : SipHash.Hoist)
    (l5 l6 l7 l8 w14 w16 w17 w24 l25 l27 : Value)
    {values : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      Slices.ByteSlice 0 ctrlNew n.ctrl ∗
      Table.slotsBefore 0 ctrlNew n.slots ∗
      Table.slotCell 0 (Table.bucketAddr ctrlOld i) (some (key, value)) ∗
      (Slices.ByteSlice 0 ctrlNew
          (Table.place n idx tag (key, value)).ctrl -∗
        Table.slotsBefore 0 ctrlNew
          (Table.place n idx tag (key, value)).slots -∗
        Table.slotCell 0 (Table.bucketAddr ctrlOld i)
          (some (key, value)) -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 (counter - 1), .i32 p4],
                walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                  (.i32 maskNew)
                  (.i32 (UInt32.ofNat idx)) (.i64 (mskPred &&& msk)) w14
                  (.i64 mskPred) w16 w17
                  (.i32 (Table.bucketAddr ctrlOld i))
                  (.i32 (hashWord >>> 25)) w24 l25 l27 h,
                .i32 (counter - 1) :: values⟩,
              code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 counter, .i32 p4],
              walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                (.i32 maskNew)
                (.i32 (UInt32.ofNat idx)) (.i64 msk) w14 (.i64 mskPred)
                w16 w17 (.i32 (Table.bucketAddr ctrlOld i))
                (.i32 hashWord) w24 l25 l27 h,
              values⟩,
            writePhase code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  subst hmaskNew
  iintro ⟨Hctrl, Hslots, Hold, Hcont⟩
  have hclen : n.ctrl.length = n.buckets + 8 := hlayout.ctrl_len
  have hslen : n.slots.length = n.buckets := hlayout.slots_len
  have hbpos : 0 < n.buckets := hlayout.pos
  have hidxCtrl : idx < n.ctrl.length := by omega
  have hidx32 : idx < 2 ^ 32 := by
    have hble : n.buckets ≤ 2 ^ 32 := by
      rw [hbShape]; exact Nat.pow_le_pow_right (by decide) hm
    omega
  have hi2lt : Table.index2 n.buckets idx < n.ctrl.length := by
    have := Nat.mod_lt (idx + 2 ^ 32 - 8) hbpos
    unfold Table.index2 Table.wrapSub
    omega
  have hi2set : Table.index2 n.buckets idx < (n.ctrl.set idx tag).length := by
    rw [List.length_set]; exact hi2lt
  have hnewNat := Table.bucketAddr_toNat ctrlNew hidx hroom
  have hctrlLt := UInt32.toNat_lt ctrlNew
  have hnewFits : (Table.bucketAddr ctrlNew idx).toNat + 8 ≤ UInt32.size := by
    simp only [UInt32.size] at *
    omega
  have hfNew := offset_facts64 (Table.bucketAddr ctrlNew idx) 0 0 rfl
    (by omega)
  have hfOld := offset_facts64 (Table.bucketAddr ctrlOld i) 0 0 rfl
    (by omega)
  have hslotNone : n.slotAt idx = none :=
    hlayout.slotAt_eq_none hidx (by rw [hempty]; decide)
  simp only [writePhase, walkLocals, rawLocals]
  -- WAT 4045 to 4048: the mask step
  wasm_twp_pures [twp_localGet twp_localGet twp_andI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  -- WAT 4049 to 4056: the tag byte at the insert index
  wasm_twp_pures [twp_localGet twp_localGet twp_add twp_localGet twp_const
    twp_shrU]
    rewriting [shrU32Wasm25, UInt32.add_comm (UInt32.ofNat idx) ctrlNew]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave ⟨Hbyte, Hclose⟩ := Func15Insert.byteFocusSet 0 ctrlNew n.ctrl
    hidxCtrl tag $$ Hctrl
  wasm_twp_rebind Wasm.SmallStep.twp_store8_addr_gen
    (n.ctrl.getD idx Table.EMPTY) with Hbyte
  isimp only [htag] at Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  -- WAT 4057 to 4067: the tag byte at the mirror
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add twp_localGet
    twp_and twp_add twp_const twp_add twp_localGet]
    rewriting [Func15Insert.index2_addr_of_wasm n hm hbShape ctrlNew hidx32]
  ihave ⟨Hbyte, Hclose⟩ := Func15Insert.byteFocusSet 0 ctrlNew
    (n.ctrl.set idx tag) hi2set tag $$ Hctrl
  wasm_twp_rebind Wasm.SmallStep.twp_store8_addr_gen
    ((n.ctrl.set idx tag).getD (Table.index2 n.buckets idx) Table.EMPTY)
    with Hbyte
  isimp only [htag] at Hbyte
  ihave Hctrl := Hclose $$ Hbyte
  -- WAT 4068 to 4077: the eight-byte move of the old bucket
  ihave ⟨Hpre, Hcell, Hpost⟩ :=
    (Table.slotsBefore_focus (i := idx) 0 ctrlNew n.slots (by omega)).mp
      $$ Hslots
  isimp only [show n.slots[idx]'(by omega) = n.slotAt idx from by
    rw [Table.slotAt, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega : idx < n.slots.length)]
    rfl, hslotNone] at Hcell
  icases slotCell_none_to_u64 0 (Table.bucketAddr ctrlNew idx) $$ Hcell with
    ⟨%oldWord, Hcell⟩
  ihave Hold := (slotCell_some_as_u64 0 (Table.bucketAddr ctrlOld i) key
    value).mp $$ Hold
  wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_sub
    twp_const twp_add]
    rewriting [shl32Wasm3, negEightAdd, slotAddr_of_wasm]
  wasm_twp_pures [twp_localGet]
  ihave Hold := wordMove64 (UInt32.add_zero (Table.bucketAddr ctrlOld i))
    $$ Hold
  wasm_twp_rebind Wasm.SmallStep.twp_load64
    (address := Table.bucketAddr ctrlOld i) (offset := 0)
    (wordPair key value)
    hfOld.1 hfOld.2.1 hfOld.2.2.1 hfOld.2.2.2.1
    hfOld.2.2.2.2.1 hfOld.2.2.2.2.2.1 hfOld.2.2.2.2.2.2.1
    hfOld.2.2.2.2.2.2.2 with Hold
  ihave Hcell := wordMove64 (UInt32.add_zero (Table.bucketAddr ctrlNew idx))
    $$ Hcell
  wasm_twp_rebind Wasm.SmallStep.twp_store64
    (address := Table.bucketAddr ctrlNew idx) (offset := 0) oldWord
    hfNew.1 hfNew.2.1 hfNew.2.2.1 hfNew.2.2.2.1
    hfNew.2.2.2.2.1 hfNew.2.2.2.2.2.1 hfNew.2.2.2.2.2.2.1
    hfNew.2.2.2.2.2.2.2 with Hcell
  ihave Hold :=
    wordMove64 (UInt32.add_zero (Table.bucketAddr ctrlOld i)).symm $$ Hold
  ihave Hcell :=
    wordMove64 (UInt32.add_zero (Table.bucketAddr ctrlNew idx)).symm $$ Hcell
  ihave Hold := (slotCell_some_as_u64 0 (Table.bucketAddr ctrlOld i) key
    value).mpr $$ Hold
  ihave Hcell := (slotCell_some_as_u64 0 (Table.bucketAddr ctrlNew idx) key
    value).mpr $$ Hcell
  ihave Hslots := (Table.slotsBefore_set (i := idx) 0 ctrlNew n.slots
      (by omega)
    (some (key, value))).mpr $$ [Hpre Hcell Hpost]
  · isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hcell]
      · iexact Hcell
      · iexact Hpost
  -- WAT 4078 to 4081: the counter
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [negOneAdd counter]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  isimp only [place_ctrl, place_slots] at Hcont
  iapply Hcont $$ Hctrl Hslots Hold

/-! ## The walk loop, WAT 3796 to 4083 -/

/-- `UInt32.ofNat` of a predecessor. -/
theorem ofNat_sub_one {a : Nat} (h1 : 1 ≤ a) (h2 : a < 4294967296) :
    UInt32.ofNat a - 1 = UInt32.ofNat (a - 1) := by
  have hsize : UInt32.size = 4294967296 := rfl
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_sub, UInt32.toNat_ofNat_of_lt' (by omega),
    UInt32.toNat_ofNat_of_lt' (by omega),
    show (1 : UInt32).toNat = 1 from rfl]
  omega

/-- A positive count is not the zero word. -/
theorem ofNat_ne_zero (n : Nat) (h : 0 < n) (hlt : n < 4294967296) :
    UInt32.ofNat n ≠ 0 := by
  have hsize : UInt32.size = 4294967296 := rfl
  intro h0
  have := congrArg UInt32.toNat h0
  rw [UInt32.toNat_ofNat_of_lt' (by rw [hsize]; omega)] at this
  simp at this
  omega

/-- A mask with a set byte has a lowest set byte. -/
theorem lowestSetByte_ne_none {msk : UInt64}
    (hmask : msk &&& Table.REP80 = msk) (hne : msk ≠ 0) :
    ∃ j0, Table.lowestSetByte msk = some j0 := by
  rcases hls : Table.lowestSetByte msk with _ | j0
  · exfalso
    apply hne
    have h0 : msk &&& Table.REP80 = 0 := by
      rw [Table.eq_zero_iff_hasBit]
      intro j hj
      rw [hmask]
      unfold Table.lowestSetByte at hls
      rw [List.find?_eq_none] at hls
      exact Bool.eq_false_iff.mpr (hls j (List.mem_range.mpr hj))
    rw [hmask] at h0
    exact h0
  · exact ⟨j0, rfl⟩

/-- The fresh table after the walk moved the buckets of `l`. -/
def walkTable (hashf : UInt32 → UInt64) (t : Table UInt32 UInt32)
    (l : List Nat) : Table UInt32 UInt32 :=
  l.foldl (Table.moveStep hashf t)
    (Table.withCapacity (ResizePures.resizeCap t))

/-- The walk builds the table of the model fold. -/
theorem walkTable_full (hashf : UInt32 → UInt64) (t : Table UInt32 UInt32) :
    walkTable hashf t (Table.fullIndices t) = ResizePures.movedTable hashf t :=
  rfl

/-- One more bucket of the walk. -/
theorem walkTable_snoc (hashf : UInt32 → UInt64) (t : Table UInt32 UInt32)
    (l : List Nat) (i : Nat) :
    walkTable hashf t (l ++ [i])
      = Table.moveStep hashf t (walkTable hashf t l) i := by
  unfold walkTable
  rw [List.foldl_append, List.foldl_cons, List.foldl_nil]

/-- The index of the walk loop.  Locals 12, 14 to 17, 22, 23, 24 and 27
are scratch words that one turn writes and the next turn reads back. -/
structure WalkIdx where
  /-- The group of the old table that the walk holds. -/
  grp : Nat
  /-- The mask of the buckets of that group that are left. -/
  msk : UInt64
  /-- The buckets that the walk moved. -/
  done : List Nat
  /-- Local 12. -/
  w12 : Value
  /-- Local 14. -/
  w14 : Value
  /-- Local 15. -/
  w15 : Value
  /-- Local 16. -/
  w16 : Value
  /-- Local 17. -/
  w17 : Value
  /-- Local 22. -/
  w22 : Value
  /-- Local 23. -/
  w23 : Value
  /-- Local 24. -/
  w24 : Value
  /-- Local 27. -/
  w27 : Value

set_option maxHeartbeats 8000000 in
/-- The walk of the resize, WAT 3796 to 4083.  Every turn moves one full
bucket of the old table into the fresh table, in the order of
`ResizePures.walkFrom`.  The loop ends when the counter of local 3 reaches
zero, and the fresh table then holds every entry of the old one. -/
theorem twp_resize_walk [WasmSmallStepGS hlc Universal.State]
    (t : Table UInt32 UInt32) (k0 k1 : UInt64)
    (hashf : UInt32 → UInt64) (hhash : hashf = SipHash.hashU32 k0 k1)
    (hwf : Table.WF hashf t) (hcl : Table.Clean t)
    (hg : t.growthLeft = 0)
    (hmax : t.items + 1 ≤ maxTableCapacity) (hone : 1 ≤ t.items)
    (m : Nat) (hm : m ≤ 32)
    (hbShape : Table.capBuckets (ResizePures.resizeCap t) = 2 ^ m)
    (ctrlNew ctrlOld : UInt32)
    (hroomNew : 8 * Table.capBuckets (ResizePures.resizeCap t)
      ≤ ctrlNew.toNat)
    (hroomOld : 8 * t.buckets ≤ ctrlOld.toNat)
    (h : SipHash.Hoist) (hh : h = SipHash.hoist k0 k1)
    (p0 p1 : UInt32) (l5 l6 l7 l8 l25 : Value)
    (w12 w14 w15 w16 w17 w22 w23 w24 w27 : Value)
    {contCode : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp} :
    ⊢@{HeapIProp} (iprop%
      (Slices.ByteSlice 0 ctrlOld t.ctrl -∗
      Table.slotsBefore 0 ctrlOld t.slots -∗
      Slices.ByteSlice 0 ctrlNew (walkTable hashf t []).ctrl -∗
      Table.slotsBefore 0 ctrlNew (walkTable hashf t []).slots -∗
      (∀ (v2 v4 : UInt32)
          (v12 v13 v14 v15 v16 v17 v22 v23 v24 v27 : Value),
        Slices.ByteSlice 0 ctrlOld t.ctrl -∗
        Table.slotsBefore 0 ctrlOld t.slots -∗
        Slices.ByteSlice 0 ctrlNew
          (walkTable hashf t (Table.fullIndices t)).ctrl -∗
        Table.slotsBefore 0 ctrlNew
          (walkTable hashf t (Table.fullIndices t)).slots -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 v2, .i32 0, .i32 v4],
                walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                  (.i32 (UInt32.ofNat
                    (Table.capBuckets (ResizePures.resizeCap t) - 1)))
                  v12 v13 v14 v15 v16 v17 v22 v23 v24 l25 v27 h,
                []⟩,
              contCode, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }]) -∗
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * 0)),
              .i32 (UInt32.ofNat t.items),
              .i32 (ctrlOld + UInt32.ofNat (8 * 0))],
              walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                (.i32 (UInt32.ofNat
                  (Table.capBuckets (ResizePures.resizeCap t) - 1)))
                w12
                (.i64 (Table.swarMatchFull
                  (Table.groupWord (Table.groupAt t 0))))
                w14 w15 w16 w17 w22 w23 w24 l25 w27 h,
              []⟩,
            Instruction.loop 0 0 walkBody :: contCode, arity, remainder,
            controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])) := by
  iintro HctrlOld HslotsOld HctrlNew HslotsNew Hexit
  subst hhash
  have hlayout : Table.Layout (SipHash.hashU32 k0 k1) t := hwf.toLayout
  have hmaxEq : maxTableCapacity = 117440512 := rfl
  obtain ⟨hcapLe, hcapOne⟩ := ResizePures.resize_buckets_bound hcl hg hmax
  rw [hmaxEq] at hcapLe
  have hbound : ResizePures.resizeCap t * 8 / 7 ≤ 2 ^ 32 := by
    have h1 : ResizePures.resizeCap t * 8 ≤ 939524096 := by omega
    have h2 : ResizePures.resizeCap t * 8 / 7 ≤ 939524096 :=
      Nat.le_trans (Nat.div_le_self _ 7) h1
    have h3 : (939524096 : Nat) ≤ 2 ^ 32 := by norm_num
    omega
  obtain ⟨hshape, hcapLe2⟩ :=
    Table.capBuckets_spec (cap := ResizePures.resizeCap t) hbound
  have hitems : t.items
      ≤ Table.bucketMaskToCapacity
          (Table.capBuckets (ResizePures.resizeCap t) - 1) := by
    have := ResizePures.resizeCap_eq_items_succ hcl hg
    omega
  have hcap : (Table.toList t).length
      ≤ Table.bucketMaskToCapacity
          (Table.capBuckets (ResizePures.resizeCap t) - 1) := by
    rw [← hwf.items_eq]; exact hitems
  have hinv0 : Table.MoveInv (SipHash.hashU32 k0 k1) t
      (Table.capBuckets (ResizePures.resizeCap t)) []
      (walkTable (SipHash.hashU32 k0 k1) t []) :=
    ResizePures.moveInv_start t hshape
  have hN0 : 0 < ResizePures.walkGroups t := by
    unfold ResizePures.walkGroups
    by_cases hsmall : t.buckets < 8
    · rw [if_pos hsmall]; omega
    · rw [if_neg hsmall]
      have := hlayout.pos
      omega
  have hmask0 : Table.swarMatchFull
        (Table.groupWord (Table.groupAt t 0)) &&& Table.REP80
      = Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)) :=
    swarMatchFull_and_REP80 _
  have hrem0 : ResizePures.walkRem t (ResizePures.walkGroups t) 0
      (Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)))
      = Table.fullIndices t := by
    rw [show (0 : Nat) = 8 * 0 from rfl] at hmask0 ⊢
    rw [ResizePures.walkRem_full t hN0]
    exact ResizePures.walkFrom_zero hlayout
  have hlenIdx : (Table.fullIndices t).length = t.items := by
    rw [Table.length_fullIndices hlayout, ← hwf.items_eq]
  have hcnt0 : (ResizePures.walkRem t (ResizePures.walkGroups t) 0
      (Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)))).length
      = t.items := by rw [hrem0, hlenIdx]
  have hne0 : ResizePures.walkRem t (ResizePures.walkGroups t) 0
      (Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)))
      ≠ [] := by
    intro hnil
    rw [hnil] at hcnt0
    simp only [List.length_nil] at hcnt0
    omega
  have happ0 : [] ++ ResizePures.walkRem t (ResizePures.walkGroups t) 0
      (Table.swarMatchFull (Table.groupWord (Table.groupAt t 0)))
      = Table.fullIndices t := by rw [List.nil_append, hrem0]
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := WalkIdx)
    (measure := fun i =>
      (ResizePures.walkRem t (ResizePures.walkGroups t) i.grp i.msk).length)
    (locals := fun i =>
      { params := [.i32 p0, .i32 p1, .i32 (UInt32.ofNat (8 * i.grp)),
          .i32 (UInt32.ofNat (ResizePures.walkRem t
            (ResizePures.walkGroups t) i.grp i.msk).length),
          .i32 (ctrlOld + UInt32.ofNat (8 * i.grp))],
        locals := walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
          (.i32 (UInt32.ofNat
            (Table.capBuckets (ResizePures.resizeCap t) - 1)))
          i.w12 (.i64 i.msk) i.w14 i.w15 i.w16 i.w17 i.w22 i.w23 i.w24
          l25 i.w27 h,
        values := [] })
    (I := fun i => iprop(
      ⌜i.msk &&& Table.REP80 = i.msk ∧
        i.grp < ResizePures.walkGroups t ∧
        i.done ++ ResizePures.walkRem t (ResizePures.walkGroups t)
            i.grp i.msk = Table.fullIndices t ∧
        ResizePures.walkRem t (ResizePures.walkGroups t) i.grp i.msk
          ≠ [] ∧
        Table.MoveInv (SipHash.hashU32 k0 k1) t
          (Table.capBuckets (ResizePures.resizeCap t)) i.done
          (walkTable (SipHash.hashU32 k0 k1) t i.done)⌝ ∗
      Slices.ByteSlice 0 ctrlOld t.ctrl ∗
      Table.slotsBefore 0 ctrlOld t.slots ∗
      Slices.ByteSlice 0 ctrlNew
        (walkTable (SipHash.hashU32 k0 k1) t i.done).ctrl ∗
      Table.slotsBefore 0 ctrlNew
        (walkTable (SipHash.hashU32 k0 k1) t i.done).slots ∗
      (∀ (v2 v4 : UInt32)
          (v12 v13 v14 v15 v16 v17 v22 v23 v24 v27 : Value),
        Slices.ByteSlice 0 ctrlOld t.ctrl -∗
        Table.slotsBefore 0 ctrlOld t.slots -∗
        Slices.ByteSlice 0 ctrlNew
          (walkTable (SipHash.hashU32 k0 k1) t
            (Table.fullIndices t)).ctrl -∗
        Table.slotsBefore 0 ctrlNew
          (walkTable (SipHash.hashU32 k0 k1) t
            (Table.fullIndices t)).slots -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 v2, .i32 0, .i32 v4],
                walkLocals l5 l6 l7 l8 (.i32 ctrlNew) (.i32 ctrlOld)
                  (.i32 (UInt32.ofNat
                    (Table.capBuckets (ResizePures.resizeCap t) - 1)))
                  v12 v13 v14 v15 v16 v17 v22 v23 v24 l25 v27 h,
                []⟩,
              contCode, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])))
    (initial := ⟨0, Table.swarMatchFull
        (Table.groupWord (Table.groupAt t 0)), [], w12, w14, w15, w16,
        w17, w22, w23, w24, w27⟩)
    (initialLocals := _) (belowStack := ([] : List Value))
  · dsimp only
    rw [hcnt0]
  · rfl
  · intro i
    iintro Hrec ⟨%hinv, HctrlOld, HslotsOld, HctrlNew, HslotsNew, Hexit⟩
    obtain ⟨hmaskI, hgrpI, happI, hneI, hinvI⟩ := hinv
    simp only [Wasm.SmallStep.loopBodyExpr, shape_walk_turn]
    iapply (twp_resize_adv (t := t) (hlayout := hlayout)
      (ctrlOld := ctrlOld) (b := i.grp) (msk := i.msk) (hmask := hmaskI)
      (hb := hgrpI) (hwork := hneI)) $$ HctrlOld
    iintro %bb %mskb %hfacts HctrlOld
    obtain ⟨hble, hbLt, hmskNe, hmskMask, hremEq⟩ := hfacts
    obtain ⟨j0, hlow⟩ := lowestSetByte_ne_none hmskMask hmskNe
    have hcons := ResizePures.walkRem_cons t (ResizePures.walkGroups t)
      bb hmskMask hlow
    have hlist : i.done ++ (8 * bb + j0) ::
        ResizePures.walkRem t (ResizePures.walkGroups t) bb
          (mskb &&& (mskb + 18446744073709551615))
        = Table.fullIndices t := by
      rw [← hcons, hremEq]; exact happI
    obtain ⟨kk, vv, hslot, hidxLt, hidxEmpty, hwin, hstep⟩ :=
      ResizePures.moveStep_spec hlayout hcap hlist hinvI
    have hmemIdx : (8 * bb + j0) ∈ Table.fullIndices t := by
      rw [← hlist]
      exact List.mem_append_right _ List.mem_cons_self
    obtain ⟨hidxOldB, hidxOldF⟩ := Table.mem_fullIndices.1 hmemIdx
    have hslotsLen : t.slots.length = t.buckets := hlayout.slots_len
    have hget : t.slots[8 * bb + j0]'(by omega) = some (kk, vv) := by
      unfold Table.slotAt at hslot
      rw [← List.getD_eq_getElem t.slots none (by omega)]
      exact hslot
    have hbucketsLe : t.buckets ≤ 2 ^ 32 := by
      obtain ⟨mm, hmm, -, hpow⟩ := hlayout.shape
      rw [hpow]
      exact Nat.pow_le_pow_right (by decide) hmm
    have hsz : UInt32.size = 4294967296 := rfl
    have hctrlOldLt : ctrlOld.toNat < 4294967296 := ctrlOld.toBitVec.isLt
    have hfits8 : (Table.bucketAddr ctrlOld (8 * bb + j0)).toNat + 8
        ≤ UInt32.size := by
      rw [Table.bucketAddr_toNat ctrlOld hidxOldB hroomOld]
      omega
    have hinvK := hinvI
    obtain ⟨hlayN, hbN, hspN, hpermN⟩ := hinvI
    have hdoneLt : i.done.length < (Table.fullIndices t).length := by
      rw [← hlist, List.length_append, List.length_cons]
      omega
    have hcapLt : Table.bucketMaskToCapacity
        (Table.capBuckets (ResizePures.resizeCap t) - 1)
        < Table.capBuckets (ResizePures.resizeCap t) := hshape.cap_lt
    have hlenN : (Table.toList
        (walkTable (SipHash.hashU32 k0 k1) t i.done)).length
        < (walkTable (SipHash.hashU32 k0 k1) t i.done).buckets := by
      have h1 := hpermN.length_eq
      have h2 : (i.done.filterMap t.slotAt).length ≤ i.done.length :=
        List.length_filterMap_le t.slotAt i.done
      rw [hbN]
      omega
    ihave ⟨HpreS, Hcell, HpostS⟩ :=
      (Table.slotsBefore_focus 0 ctrlOld t.slots
        (i := 8 * bb + j0) (by omega)).mp $$ HslotsOld
    isimp only [hget, Table.slotCell] at Hcell
    icases Hcell with ⟨Hkey, Hvalue⟩
    iapply Wasm.SmallStep.twp_block
    simp only [List.drop_zero, shape_hash_body]
    iapply (twp_resize_addr (msk := mskb) (j0 := j0) (b := bb)
      (i := 8 * bb + j0) (key := kk) (hmask := hmskMask) (hlow := hlow)
      (hi := rfl) (hib := by omega) (hbucketFits := by omega))
    isplitl [Hkey]
    · iexact Hkey
    · iintro Hkey
      iapply (twp_resize_hash k0 k1 kk h hh)
      iintro %a14 %a15 %a16 %a17 %a24
      simp only [shape_probe_phase]
      iapply (twp_resize_probe
        (n := walkTable (SipHash.hashU32 k0 k1) t i.done) (m := m)
        (hm := hm) (hbShape := by rw [hbN]; exact hbShape)
        (hlay := hlayN) (hsp := hspN) (hlen := hlenN)
        (hsh := SipHash.hashU32 k0 k1 kk)
        (hword := SipHash.hashU32Low k0 k1 kk)
        (hcompat := toUInt32_hashLow k0 k1 kk)
        (maskNew := UInt32.ofNat
          (Table.capBuckets (ResizePures.resizeCap t) - 1))
        (hmaskNew := by rw [hbN])) $$ HctrlNew
      iintro %pos %j1 %mskP %v27 %hprobe HctrlNew
      obtain ⟨hmaskP, hlowP, hspecialP, hfindP⟩ := hprobe
      wasm_twp_pures [twp_localGet twp_constI64 twp_addI64]
      wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.reduceSub]
      iapply (twp_resize_fix
        (n := walkTable (SipHash.hashU32 k0 k1) t i.done) (m := m)
        (hm := hm) (hbShape := by rw [hbN]; exact hbShape)
        (hlay := hlayN) (hclean := hspN) (hlen := hlenN)
        (msk := mskP) (pos := pos) (j0 := j1)
        (c := (pos + j1)
          % (walkTable (SipHash.hashU32 k0 k1) t i.done).buckets)
        (hmask := hmaskP) (hlow := hlowP) (hc := rfl)
        (hspecial := hspecialP)
        (maskNew := UInt32.ofNat
          (Table.capBuckets (ResizePures.resizeCap t) - 1))
        (hmaskNew := by rw [hbN]))
      isplitl [HctrlNew]
      · iexact HctrlNew
      · iintro HctrlNew
        isimp only [← hfindP]
        simp only [shape_write_phase]
        iapply (twp_resize_write
          (n := walkTable (SipHash.hashU32 k0 k1) t i.done)
          (hlayout := hlayN) (m := m) (hm := hm)
          (hbShape := by rw [hbN]; exact hbShape)
          (idx := Table.findInsertIndex
            (walkTable (SipHash.hashU32 k0 k1) t i.done)
            (SipHash.hashU32 k0 k1 kk))
          (i := 8 * bb + j0) (hidx := hidxLt) (hempty := hidxEmpty)
          (tag := Table.h2 (SipHash.hashU32 k0 k1 kk))
          (hashWord := (SipHash.hashU32Low k0 k1 kk).toUInt32)
          (htag := by rw [tagByte_of_low, ← Table.h2_hashU32Low])
          (key := kk) (value := vv)
          (maskNew := UInt32.ofNat
            (Table.capBuckets (ResizePures.resizeCap t) - 1))
          (hmaskNew := by rw [hbN])
          (msk := mskb) (mskPred := mskb + 18446744073709551615)
          (hroom := by rw [hbN]; exact hroomNew)
          (holdFits := hfits8))
        isplitl [HctrlNew]
        · iexact HctrlNew
        · isplitl [HslotsNew]
          · iexact HslotsNew
          · isplitl [Hkey Hvalue]
            · isimp only [Table.slotCell]
              isplitl [Hkey]
              · iexact Hkey
              · iexact Hvalue
            · iintro HctrlNew HslotsNew Hcell
              ihave HslotsOld : Table.slotsBefore 0 ctrlOld t.slots
                  $$ [HpreS Hcell HpostS]
              · iapply (Table.slotsBefore_focus 0 ctrlOld t.slots
                  (i := 8 * bb + j0) (by omega)).mpr
                isplitl [HpreS]
                · iexact HpreS
                · isplitl [Hcell]
                  · isimp only [hget]
                    iexact Hcell
                  · iexact HpostS
              have hremCons : ResizePures.walkRem t
                  (ResizePures.walkGroups t) i.grp i.msk
                  = (8 * bb + j0) :: ResizePures.walkRem t
                      (ResizePures.walkGroups t) bb
                      (mskb &&& (mskb + 18446744073709551615)) := by
                rw [← hremEq]; exact hcons
              have hcomm : (mskb + 18446744073709551615) &&& mskb
                  = mskb &&& (mskb + 18446744073709551615) :=
                UInt64.and_comm _ _
              have hp32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
              have hcapLe32 : Table.capBuckets (ResizePures.resizeCap t)
                  ≤ 2 ^ 32 := by
                rw [hbShape]
                exact Nat.pow_le_pow_right (by decide) hm
              have hremLe : (ResizePures.walkRem t
                  (ResizePures.walkGroups t) i.grp i.msk).length
                  ≤ (Table.fullIndices t).length := by
                rw [← happI, List.length_append]
                omega
              rw [hlenIdx] at hremLe
              have hremLt : (ResizePures.walkRem t
                  (ResizePures.walkGroups t) i.grp i.msk).length
                  < 4294967296 := by omega
              isimp only [hcomm]
              rcases hrest : ResizePures.walkRem t
                  (ResizePures.walkGroups t) bb
                  (mskb &&& (mskb + 18446744073709551615)) with _ | ⟨x, xs⟩
              · have hlen1 : (ResizePures.walkRem t
                    (ResizePures.walkGroups t) i.grp i.msk).length = 1 := by
                  rw [hremCons, hrest]; rfl
                have hz1 : UInt32.ofNat 1 - 1 = (0 : UInt32) := rfl
                have hfinal : i.done ++ [8 * bb + j0]
                    = Table.fullIndices t := by
                  rw [← hlist, hrest]
                have hfin : Table.place
                      (walkTable (SipHash.hashU32 k0 k1) t i.done)
                      (Table.findInsertIndex
                        (walkTable (SipHash.hashU32 k0 k1) t i.done)
                        (SipHash.hashU32 k0 k1 kk))
                      (Table.h2 (SipHash.hashU32 k0 k1 kk)) (kk, vv)
                    = walkTable (SipHash.hashU32 k0 k1) t
                        (Table.fullIndices t) := by
                  rw [← hfinal, walkTable_snoc, hstep]
                isimp only [hfin] at HctrlNew HslotsNew
                isimp only [hlen1, hz1]
                iapply Wasm.SmallStep.twp_brIfZero
                iapply Wasm.SmallStep.twp_exitControl (by rfl)
                simp only [List.take_zero, List.nil_append]
                iapply Hexit $$ HctrlOld HslotsOld HctrlNew HslotsNew
              · have hlenS : (ResizePures.walkRem t
                    (ResizePures.walkGroups t) i.grp i.msk).length
                    = xs.length + 2 := by
                  rw [hremCons, hrest]
                  simp only [List.length_cons]
                have hcntEq : UInt32.ofNat (ResizePures.walkRem t
                      (ResizePures.walkGroups t) i.grp i.msk).length - 1
                    = UInt32.ofNat (ResizePures.walkRem t
                      (ResizePures.walkGroups t) bb
                      (mskb &&& (mskb + 18446744073709551615))).length := by
                  rw [hlenS, hrest, ofNat_sub_one (by omega) (by omega)]
                  simp only [List.length_cons]
                  congr 1
                have hnz : UInt32.ofNat (ResizePures.walkRem t
                    (ResizePures.walkGroups t) bb
                    (mskb &&& (mskb + 18446744073709551615))).length
                    ≠ 0 := by
                  rw [hrest]
                  simp only [List.length_cons]
                  exact ofNat_ne_zero _ (by omega) (by omega)
                have hmaskNext : (mskb &&& (mskb + 18446744073709551615))
                    &&& Table.REP80
                    = mskb &&& (mskb + 18446744073709551615) := by
                  rw [UInt64.and_assoc, UInt64.and_comm _ Table.REP80,
                    ← UInt64.and_assoc, hmskMask]
                have happNext : (i.done ++ [8 * bb + j0]) ++
                    ResizePures.walkRem t (ResizePures.walkGroups t) bb
                      (mskb &&& (mskb + 18446744073709551615))
                    = Table.fullIndices t := by
                  rw [List.append_assoc, List.singleton_append]
                  exact hlist
                have hneNext : ResizePures.walkRem t
                    (ResizePures.walkGroups t) bb
                    (mskb &&& (mskb + 18446744073709551615)) ≠ [] := by
                  rw [hrest]
                  exact List.cons_ne_nil _ _
                have hmeas : (ResizePures.walkRem t
                    (ResizePures.walkGroups t) bb
                    (mskb &&& (mskb + 18446744073709551615))).length
                    < (ResizePures.walkRem t (ResizePures.walkGroups t)
                      i.grp i.msk).length := by
                  rw [hlenS, hrest]
                  simp only [List.length_cons]
                  omega
                have hinvNext := Table.moveStep_inv hlayout hcap hlist hinvK
                have hstepSnoc : walkTable (SipHash.hashU32 k0 k1) t
                    (i.done ++ [8 * bb + j0])
                    = Table.place
                      (walkTable (SipHash.hashU32 k0 k1) t i.done)
                      (Table.findInsertIndex
                        (walkTable (SipHash.hashU32 k0 k1) t i.done)
                        (SipHash.hashU32 k0 k1 kk))
                      (Table.h2 (SipHash.hashU32 k0 k1 kk)) (kk, vv) := by
                  rw [walkTable_snoc, hstep]
                rw [← walkTable_snoc] at hinvNext
                isimp only [hcntEq]
                iapply Wasm.SmallStep.twp_brIf hnz (by rfl)
                simp only [List.take_zero, List.nil_append]
                simp only [← shape_probe_phase, ← shape_hash_body,
                  ← shape_write_phase, ← shape_walk_turn]
                ihave Hback := Hrec
                  $$ %((⟨bb, mskb &&& (mskb + 18446744073709551615),
                      i.done ++ [8 * bb + j0],
                      .i32 (UInt32.ofNat (Table.findInsertIndex
                        (walkTable (SipHash.hashU32 k0 k1) t i.done)
                        (SipHash.hashU32 k0 k1 kk))),
                      .i64 mskP, .i64 (mskb + 18446744073709551615),
                      .i64 a16, .i64 a17,
                      .i32 (Table.bucketAddr ctrlOld (8 * bb + j0)),
                      .i32 ((SipHash.hashU32Low k0 k1 kk).toUInt32 >>> 25),
                      .i64 a24, v27⟩ : WalkIdx))
                  %hmeas
                ieval (dsimp only) at Hback
                iapply Hback
                isplitl_pureexact ⟨hmaskNext, hbLt, happNext, hneNext,
                  hinvNext⟩
                isimp only [hstepSnoc]
                iframe HctrlOld HslotsOld HctrlNew HslotsNew Hexit
  · isplitl_pureexact ⟨hmask0, hN0, happ0, hne0, hinv0⟩
    iframe HctrlOld HslotsOld HctrlNew HslotsNew Hexit

/-! ## The hoisted block, WAT 3750 to 3795 -/

/-- `REP80` as the compiled code writes it. -/
theorem repEighty : (9259542123273814144 : UInt64) = Table.REP80 := rfl

/-- The first group mask, as WAT 3785 to 3788 builds it: the complement is
`xor` with the all-ones word. -/
theorem swarMatchFull_of_wasm (g : UInt64) :
    (g ^^^ 18446744073709551615) &&& 9259542123273814144
      = Table.swarMatchFull g := by
  rw [repEighty, ← Table.not_eq_xor_neg_one]
  rfl

set_option maxHeartbeats 2000000 in
/-- The block above the walk loop, WAT 3750 to 3795.  It reads the two
seed words of the `RandomState`, computes the five hoisted words, reads
the first group of the old control bytes into the mask register, and
starts the three loop registers: the old cursor in param 4, the group
offset in param 2 and the item counter in param 3. -/
theorem twp_resize_hoist [WasmSmallStepGS hlc Universal.State]
    (k0 k1 g : UInt64) (p0 p1 p2 hasher p4 ctrlOld items : UInt32)
    (l5 l7 l8 l9 l11 l12 w13 w14 w15 w16 w17 w18 w19 w20 w21 l22 l23 w24
      l25 w26 l27 : Value)
    {values : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hhasher : hasher.toNat + 16 ≤ UInt32.size)
    (hctrlOld : ctrlOld.toNat + 8 ≤ UInt32.size) :
    iprop(
      pointsTo_u64 0 hasher k0 ∗
      pointsTo_u64 0 (hasher + 8) k1 ∗
      pointsTo_u64 0 ctrlOld g ∗
      (∀ (a14 a15 a16 : UInt64),
        pointsTo_u64 0 hasher k0 -∗
        pointsTo_u64 0 (hasher + 8) k1 -∗
        pointsTo_u64 0 ctrlOld g -∗
        WP (.running
            ⟨⟨[.i32 p0, .i32 p1, .i32 0, .i32 items, .i32 ctrlOld],
                walkLocals l5 (.i32 items) l7 l8 l9 (.i32 ctrlOld) l11 l12
                  (.i64 (Table.swarMatchFull g)) (.i64 a14) (.i64 a15)
                  (.i64 a16) w17 l22 l23 w24 l25 l27 (hoistWasm k0 k1),
                values⟩,
              code, arity, remainder, controls, calls⟩ :
            Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 p0, .i32 p1, .i32 p2, .i32 hasher, .i32 p4],
              rawLocals l5 (.i32 items) l7 l8 l9 (.i32 ctrlOld) l11 l12
                w13 w14 w15 w16 w17 w18 w19 w20 w21 l22 l23 w24 l25 w26
                l27,
              values⟩,
            hoistPhase code, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hk0, Hk1, Hg, Hcont⟩
  have hfa0 := offset_facts64 hasher 0 0 rfl (by omega)
  have hfa1 := offset_facts64 hasher 8 8 rfl (by omega)
  have hfg := offset_facts64 ctrlOld 0 0 rfl (by omega)
  simp only [hoistPhase, rawLocals]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := hasher)
    (offset := 8) k1
    hfa1.1 hfa1.2.1 hfa1.2.2.1 hfa1.2.2.2.1
    hfa1.2.2.2.2.1 hfa1.2.2.2.2.2.1 hfa1.2.2.2.2.2.2.1
    hfa1.2.2.2.2.2.2.2 with Hk1
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  ihave Hk0 := wordMove64 (UInt32.add_zero hasher) $$ Hk0
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := hasher)
    (offset := 0) k0
    hfa0.1 hfa0.2.1 hfa0.2.2.1 hfa0.2.2.2.1
    hfa0.2.2.2.2.1 hfa0.2.2.2.2.2.1 hfa0.2.2.2.2.2.2.1
    hfa0.2.2.2.2.2.2.2 with Hk0
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_xorI64 twp_addI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_rotlI64 twp_localGet
    twp_xorI64]
  wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_constI64 twp_rotlI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet twp_constI64 twp_xorI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  ihave Hg := wordMove64 (UInt32.add_zero ctrlOld) $$ Hg
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := ctrlOld)
    (offset := 0) g
    hfg.1 hfg.2.1 hfg.2.2.1 hfg.2.2.2.1
    hfg.2.2.2.2.1 hfg.2.2.2.2.2.1 hfg.2.2.2.2.2.2.1
    hfg.2.2.2.2.2.2.2 with Hg
  wasm_twp_pures [twp_constI64 twp_xorI64 twp_constI64 twp_andI64]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_const]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  wasm_twp_pures [twp_localGet]
  wasm_twp_localSet [List.set, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub]
  ihave Hk0 := wordMove64 (UInt32.add_zero hasher).symm $$ Hk0
  ihave Hg := wordMove64 (UInt32.add_zero ctrlOld).symm $$ Hg
  isimp only [walkLocals, rawLocals, hoistWasm] at Hcont
  isimp only [rotlWasm13, rotlWasm17, rotlWasm32, swarMatchFull_of_wasm]
  iapply Hcont $$ %(k1 ^^^ 7237128888997146477) %k0
    %((k1 ^^^ 7237128888997146477) + (k0 ^^^ 8317987319222330741))
    Hk0 Hk1 Hg

end Project.RustHashMap.Func14ResizeWalk
