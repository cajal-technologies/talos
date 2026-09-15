import Project.RustHashMap.MapOpContracts
import Project.RustHashMap.LookupPures
import Project.RustHashMap.FrameCells

/-!
# Proof of the `insert` shim, absolute `func 6`

This file proves local `func3`, absolute `func 6`, against
`Project.RustHashMap.MapOpContracts.Func3Spec`.  The body is WAT lines
975 to 1021 of `programs/rust/build/rust_hash_map/program.wat`.

The body is a shim.  It commits a 16-byte frame, calls `HashMap::insert`,
absolute `func 18`, with the 8-byte slot at `frame + 8` as the
`Option<u32>` out-parameter, and then builds the 40-byte answer of
`map_insert`.  It has no guard, no loop and no dead arm, so the proof is
one straight line.

## The moves

| WAT | Move |
| --- | --- |
| 977 to 981 | `frame := sp - 16`, and global zero takes it |
| 982 to 988 | `call 18` with `frame + 8`, the map, the key, the value |
| 989 to 991 | local 3 takes the discriminant at `frame + 8` |
| 992 to 994 | local 2 takes the payload at `frame + 12` |
| 995 to 1010 | the 32 bytes at `map` move to `out + 8`, high cell first |
| 1011 to 1013 | the payload goes to `out + 4` |
| 1014 to 1016 | the discriminant goes to `out` |
| 1017 to 1020 | global zero takes `frame + 16` back |

`Func15InsertSpec` is a hypothesis of this theorem.  Another window proves
it.  Every conjunct of its precondition comes from the precondition of
`Func3Spec`: the table facts pass through unchanged, and the two address
facts of the frame slot follow from `insertWrapDepth <= sp.toNat`.

## The stack

`Func3Spec` lends 160 bytes below `sp`.  The top 16 of them are the frame
of this body and the other 144 are `insertFullDepth`, which the call
takes.  `below_split` and `below_join` are that split.
-/

namespace Project.RustHashMap.Func3Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Wasm.RustStd Wasm.RustStd.HashMap
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.LookupPures
open Project.RustHashMap.MapOpContracts
open scoped Wasm.SmallStep.Outcome

private theorem func3_index :
    Project.RustHashMap.«module».funcs[3]? =
      some Project.RustHashMap.func3Def := by rfl

/-! ## The stack region -/

/-- Split a byte slice at a byte boundary.  Copy of
`Project.RustHashMap.Func5Proof.slice_split`, which is private there. -/
private theorem slice_split [WasmHeapGS Universal.State]
    (ptr : UInt32) (k : Nat) (bytes : List UInt8) (hk : k ≤ bytes.length) :
    Slices.ByteSlice (α := Universal.State) 0 ptr bytes ⊣⊢
      iprop(Slices.ByteSlice 0 ptr (bytes.take k) ∗
        Slices.ByteSlice 0 (ptr + UInt32.ofNat k) (bytes.drop k)) := by
  have h := Slices.ByteSlice_append (α := Universal.State) 0 ptr
    (bytes.take k) (bytes.drop k)
  rw [List.take_append_drop, List.length_take, Nat.min_eq_left hk] at h
  exact h

/-- The region below the caller holds the region of the call at the bottom
and the 16-byte frame of this body on top of it. -/
private theorem below_split [WasmHeapGS Universal.State]
    (sp : UInt32) (below : List UInt8) :
    StackBelow sp insertWrapDepth below ⊢
      iprop(⌜below.length = 160⌝ ∗
        StackBelow (sp - 16) insertFullDepth (below.take 144) ∗
        Slices.ByteSlice 0 (sp - 16) (below.drop 144)) := by
  have haddr : sp - 16 - UInt32.ofNat insertFullDepth
      = sp - UInt32.ofNat insertWrapDepth := by
    rw [show UInt32.ofNat insertFullDepth = (144 : UInt32) from rfl,
      Table.sub_sub_addr,
      show (16 : UInt32) + 144 = UInt32.ofNat insertWrapDepth from by
        decide]
  have hup : sp - UInt32.ofNat insertWrapDepth + UInt32.ofNat 144
      = sp - 16 := by
    rw [show UInt32.ofNat 144 = (144 : UInt32) from rfl,
      show UInt32.ofNat insertWrapDepth = (16 : UInt32) + 144 from by
        decide,
      ← Table.sub_sub_addr, UInt32.sub_add_cancel]
  iintro Hbelow
  isimp only [StackBelow] at Hbelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  have hlen160 : below.length = 160 := hlength
  icases (slice_split (sp - UInt32.ofNat insertWrapDepth) 144 below
    (by omega)).mp $$ Hbytes with ⟨Hlow, Hhigh⟩
  isplitl_pureexact hlen160
  · isplitl [Hlow]
    · isimp only [StackBelow]
      isplitl_pureexact
        (show (below.take 144).length = insertFullDepth by
          rw [insertFullDepth_eq, List.length_take]; omega)
      · irw_exact [haddr] with Hlow
    · irw_exact [← hup] with Hhigh

/-- Put the two halves of the region back together. -/
private theorem below_join [WasmHeapGS Universal.State]
    (sp : UInt32) (low frame : List UInt8) (hframe : frame.length = 16) :
    iprop(StackBelow (sp - 16) insertFullDepth low ∗
        Slices.ByteSlice 0 (sp - 16) frame) ⊢
      StackBelow sp insertWrapDepth (low ++ frame) := by
  have haddr : sp - 16 - UInt32.ofNat insertFullDepth
      = sp - UInt32.ofNat insertWrapDepth := by
    rw [show UInt32.ofNat insertFullDepth = (144 : UInt32) from rfl,
      Table.sub_sub_addr,
      show (16 : UInt32) + 144 = UInt32.ofNat insertWrapDepth from by
        decide]
  iintro ⟨Hlow, Hframe⟩
  isimp only [StackBelow] at Hlow
  icases Hlow with ⟨%hlen, Hlow⟩
  have hlow : low.length = 144 := by
    rw [insertFullDepth_eq] at hlen; exact hlen
  have hup : sp - UInt32.ofNat insertWrapDepth + UInt32.ofNat low.length
      = sp - 16 := by
    rw [hlow, show UInt32.ofNat 144 = (144 : UInt32) from rfl,
      show UInt32.ofNat insertWrapDepth = (16 : UInt32) + 144 from by
        decide,
      ← Table.sub_sub_addr, UInt32.sub_add_cancel]
  isimp only [StackBelow]
  isplitl_pureexact
    (show (low ++ frame).length = insertWrapDepth by
      rw [List.length_append, hlow, hframe]; rfl)
  · iapply (Slices.ByteSlice_append (α := Universal.State) 0
      (sp - UInt32.ofNat insertWrapDepth) low frame).mpr
    isplitl [Hlow]
    · irw_exact [← haddr] with Hlow
    · irw_exact [hup] with Hframe

/-! ## The `Option<u32>` slot -/

/-- The inverse of
`Wasm.RustStd.HashMap.Table.optionU32At_of_words`: the slot is the
discriminant word and a payload word that is the value on the `some`
arm. -/
private theorem optionU32At_words [WasmHeapGS Universal.State]
    (addr : UInt32) (o : Option UInt32) :
    Table.optionU32At (α := Universal.State) 0 addr o ⊢
      iprop(∃ payload : UInt32,
        ⌜∀ v : UInt32, o = some v → payload = v⌝ ∗
        pointsTo_u32 0 addr (if o.isSome then 1 else 0) ∗
        pointsTo_u32 0 (addr + 4) payload) := by
  cases o with
  | none =>
      isimp only [Table.optionU32At]
      iintro ⟨%pad, Htag, Hpad⟩
      iexists pad
      isplitl_pureexact (by
        intro v hv
        exact absurd hv (by simp))
      · isimp only [Option.isSome_none, Bool.false_eq_true, if_false]
        isplitl_exact Htag
        · iexact Hpad
  | some v =>
      isimp only [Table.optionU32At]
      iintro ⟨Htag, Hval⟩
      iexists v
      isplitl_pureexact (by
        intro w hw
        exact Option.some_inj.mp hw)
      · isimp only [Option.isSome_some, if_true]
        isplitl_exact Htag
        · iexact Hval


/-! ## The answer -/

/-- The eight little-endian bytes of a double word.  Copy of
`Project.RustHashMap.Func8Proof.u64Bytes`, which is private there. -/
private def u64Bytes (v : UInt64) : List UInt8 :=
  [u64Byte v 0, u64Byte v 1, u64Byte v 2, u64Byte v 3,
    u64Byte v 4, u64Byte v 5, u64Byte v 6, u64Byte v 7]

/-- One owned double word is its eight owned bytes. -/
private theorem u64_as_bytes {α : Type} [WasmHeapGS α] (memId : Nat)
    (addr : UInt32) (v : UInt64) :
    pointsTo_u64 (α := α) memId addr v ⊣⊢
      pointsToBytes memId addr (u64Bytes v) := by
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; rfl
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; rfl
  have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; rfl
  have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; rfl
  have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; rfl
  have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; rfl
  simp only [pointsToBytes, pointsTo_u64, u64Bytes, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
  exact .rfl

/-- Four owned double words in a row are one owned 32-byte range.  Copy of
`Project.RustHashMap.Func8Proof.cells_as_slice`. -/
private theorem cells_as_slice {α : Type} [WasmHeapGS α] (memId : Nat)
    (addr : UInt32) (v0 v1 v2 v3 : UInt64)
    (hbound : addr.toNat + 32 < UInt32.size) :
    iprop(pointsTo_u64 (α := α) memId addr v0 ∗
      pointsTo_u64 memId (addr + 8) v1 ∗
      pointsTo_u64 memId (addr + 16) v2 ∗
      pointsTo_u64 memId (addr + 24) v3) ⊢
      Slices.ByteSlice memId addr
        (u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes v2
          ++ u64Bytes v3))) := by
  have e16 : addr + 8 + 8 = addr + 16 := by rw [UInt32.add_assoc]; rfl
  have e24 : addr + 16 + 8 = addr + 24 := by rw [UInt32.add_assoc]; rfl
  have e8 : (UInt32.ofNat (u64Bytes v0).length : UInt32) = 8 := rfl
  have e8' : (UInt32.ofNat (u64Bytes v1).length : UInt32) = 8 := rfl
  have e8'' : (UInt32.ofNat (u64Bytes v2).length : UInt32) = 8 := rfl
  have hlen : (u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes v2
      ++ u64Bytes v3))).length = 32 := rfl
  iintro ⟨H0, H1, H2, H3⟩
  isimp only [Slices.ByteSlice, hlen]
  isplitl_pureexact hbound
  iapply (pointsToBytes_append memId addr (u64Bytes v0)
    (u64Bytes v1 ++ (u64Bytes v2 ++ u64Bytes v3))).mpr
  isimp only [e8]
  isplitl [H0]
  · iapply (u64_as_bytes memId addr v0).mp
    iexact H0
  · iapply (pointsToBytes_append memId (addr + 8) (u64Bytes v1)
      (u64Bytes v2 ++ u64Bytes v3)).mpr
    isimp only [e8', e16]
    isplitl [H1]
    · iapply (u64_as_bytes memId (addr + 8) v1).mp
      iexact H1
    · iapply (pointsToBytes_append memId (addr + 16) (u64Bytes v2)
        (u64Bytes v3)).mpr
      isimp only [e8'', e24]
      isplitl [H2]
      · iapply (u64_as_bytes memId (addr + 16) v2).mp
        iexact H2
      · iapply (u64_as_bytes memId (addr + 24) v3).mp
        iexact H3

set_option maxHeartbeats 8000000 in
/-- The answer of the shim, WAT 989 to 1016.  Local 2 and local 3 hold
the payload and the discriminant when it ends, and the frame slot keeps
its two words. -/
private theorem twp_func3_tail [WasmSmallStepGS hlc Universal.State]
    (out map frame a2 a3 : UInt32) (k0 k1 : UInt64)
    (tf : Table UInt32 UInt32) (o : Option UInt32)
    (outBefore : List UInt8)
    {cont : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset} {Φ : ObservableOutcome → HeapIProp}
    (hlength : outBefore.length = 40)
    (houtBound : out.toNat + 40 < UInt32.size)
    (hmapBound : map.toNat + 32 < UInt32.size)
    (hframeBound : frame.toNat + 16 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      Table.HashMapAt 0 map k0 k1 tf ∗
      Table.optionU32At 0 (frame + 8) o ∗
      (∀ mapBytes : List UInt8, ∀ tag : UInt32, ∀ payload : UInt32,
        ⌜mapBytes.length = 32⌝ -∗
        Table.optionU32At 0 out o -∗
        Table.HashMapAt 0 (out + 8) k0 k1 tf -∗
        Slices.ByteSlice 0 map mapBytes -∗
        pointsTo_u32 0 (frame + 8) tag -∗
        pointsTo_u32 0 (frame + 8 + 4) payload -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 map, .i32 payload, .i32 tag], [.i32 frame],
              []⟩, cont, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 map, .i32 a2, .i32 a3], [.i32 frame], []⟩,
            .localGet 4 :: .load32 8 :: .localSet 3 :: .localGet 4 ::
              .load32 12 :: .localSet 2 :: .localGet 0 :: .localGet 1 ::
              .load64 24 :: .store64 32 :: .localGet 0 :: .localGet 1 ::
              .load64 16 :: .store64 24 :: .localGet 0 :: .localGet 1 ::
              .load64 8 :: .store64 16 :: .localGet 0 :: .localGet 1 ::
              .load64 0 :: .store64 8 :: .localGet 0 :: .localGet 2 ::
              .store32 4 :: .localGet 0 :: .localGet 3 :: .store32 0 ::
              cont,
            arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hmap, Hslot, Hcont⟩
  have hsize : UInt32.size = 4294967296 := rfl
  have e16 : out + 8 + 8 = out + 16 := by rw [UInt32.add_assoc]; rfl
  have e24 : out + 8 + 16 = out + 24 := by rw [UInt32.add_assoc]; rfl
  have e32 : out + 8 + 24 = out + 32 := by rw [UInt32.add_assoc]; rfl
  have ef12 : frame + 8 + 4 = frame + 12 := by rw [UInt32.add_assoc]; rfl
  have hout8 : (out + 8).toNat = out.toNat + 8 := by
    simpa using Slices.byteOffset_toNat out 8 (by omega)
  have ho0 := FrameCells.offset_facts out 0 0 rfl (by omega)
  have ho4 := FrameCells.offset_facts out 4 4 rfl (by omega)
  have hs8 := FrameCells.offset_facts64 out 8 8 rfl (by omega)
  have hs16 := FrameCells.offset_facts64 out 16 16 rfl (by omega)
  have hs24 := FrameCells.offset_facts64 out 24 24 rfl (by omega)
  have hs32 := FrameCells.offset_facts64 out 32 32 rfl (by omega)
  have hm0 := FrameCells.offset_facts64 map 0 0 rfl (by omega)
  have hm8 := FrameCells.offset_facts64 map 8 8 rfl (by omega)
  have hm16 := FrameCells.offset_facts64 map 16 16 rfl (by omega)
  have hm24 := FrameCells.offset_facts64 map 24 24 rfl (by omega)
  have hf8 := FrameCells.offset_facts frame 8 8 rfl (by omega)
  have hf12 := FrameCells.offset_facts frame 12 12 rfl (by omega)
  -- the output slot splits into the option and the map value
  have hhead : (outBefore.take 8).length = 8 := by
    rw [List.length_take]; omega
  have htail : (outBefore.drop 8).length = 32 := by
    rw [List.length_drop]; omega
  have happ :=
    (Slices.ByteSlice_append (α := Universal.State) 0 out
      (outBefore.take 8) (outBefore.drop 8)).mp
  rw [List.take_append_drop, hhead,
    show (UInt32.ofNat 8 : UInt32) = 8 from rfl] at happ
  ihave ⟨Hlow, Hhigh⟩ := happ $$ Hout
  ihave ⟨%w0, %w1, Hw0, Hw1⟩ :=
    outWords 0 out (outBefore.take 8) hhead (by omega) $$ Hlow
  ihave ⟨%d0, %d1, %d2, %d3, Hd0, Hd1, Hd2, Hd3⟩ :=
    ByteSlice_thirtyTwo_as_cells 0 (out + 8) (outBefore.drop 8) htail
      $$ Hhigh
  isimp only [e16, e24, e32] at Hd1 Hd2 Hd3
  -- the map value splits into four cells
  ihave ⟨%v0, %v1, Hv0, Hv1, Hk0, Hk1, Hback⟩ :=
    HashMapAt_move 0 map (out + 8) k0 k1 tf $$ Hmap
  isimp only [e16, e24, e32] at Hback
  -- the frame slot splits into the two words
  ihave ⟨%payload, %hpayload, Htag, Hpay⟩ :=
    optionU32At_words (frame + 8) o $$ Hslot
  isimp only [ef12] at Hpay
  -- the discriminant and the payload leave the frame
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := frame) (offset := 8)
    (if o.isSome then 1 else 0) hf8.1 hf8.2.1 hf8.2.2.1 hf8.2.2.2 with Htag
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load32 (address := frame)
    (offset := 12) payload hf12.1 hf12.2.1 hf12.2.2.1 hf12.2.2.2 with Hpay
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- the second seed
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 24)
    k1 hm24.1 hm24.2.1 hm24.2.2.1 hm24.2.2.2.1 hm24.2.2.2.2.1
    hm24.2.2.2.2.2.1 hm24.2.2.2.2.2.2.1 hm24.2.2.2.2.2.2.2 with Hk1
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 32)
    d3 hs32.1 hs32.2.1 hs32.2.2.1 hs32.2.2.2.1 hs32.2.2.2.2.1
    hs32.2.2.2.2.2.1 hs32.2.2.2.2.2.2.1 hs32.2.2.2.2.2.2.2 with Hd3
  -- the first seed
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 16)
    k0 hm16.1 hm16.2.1 hm16.2.2.1 hm16.2.2.2.1 hm16.2.2.2.2.1
    hm16.2.2.2.2.2.1 hm16.2.2.2.2.2.2.1 hm16.2.2.2.2.2.2.2 with Hk0
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 24)
    d2 hs24.1 hs24.2.1 hs24.2.2.1 hs24.2.2.2.1 hs24.2.2.2.2.1
    hs24.2.2.2.2.2.1 hs24.2.2.2.2.2.2.1 hs24.2.2.2.2.2.2.2 with Hd2
  -- the two counters
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 8)
    v1 hm8.1 hm8.2.1 hm8.2.2.1 hm8.2.2.2.1 hm8.2.2.2.2.1
    hm8.2.2.2.2.2.1 hm8.2.2.2.2.2.2.1 hm8.2.2.2.2.2.2.2 with Hv1
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 16)
    d1 hs16.1 hs16.2.1 hs16.2.2.1 hs16.2.2.2.1 hs16.2.2.2.2.1
    hs16.2.2.2.2.2.1 hs16.2.2.2.2.2.2.1 hs16.2.2.2.2.2.2.2 with Hd1
  -- the control pointer and the bucket mask
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hv0 : pointsTo_u64 0 (map + 0) v0 $$ [Hv0]
  · irw_exact [UInt32.add_zero] with Hv0
  wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := map) (offset := 0)
    v0 hm0.1 hm0.2.1 hm0.2.2.1 hm0.2.2.2.1 hm0.2.2.2.2.1
    hm0.2.2.2.2.2.1 hm0.2.2.2.2.2.2.1 hm0.2.2.2.2.2.2.2 with Hv0
  isimp only [UInt32.add_zero] at Hv0
  wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := out) (offset := 8)
    d0 hs8.1 hs8.2.1 hs8.2.2.1 hs8.2.2.2.1 hs8.2.2.2.2.1
    hs8.2.2.2.2.2.1 hs8.2.2.2.2.2.2.1 hs8.2.2.2.2.2.2.2 with Hd0
  -- the payload and the discriminant
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out) (offset := 4)
    w1 ho4.1 ho4.2.1 ho4.2.2.1 ho4.2.2.2 with Hw1
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Hw0 : pointsTo_u32 0 (out + 0) w0 $$ [Hw0]
  · irw_exact [UInt32.add_zero] with Hw0
  wasm_twp_rebind Wasm.SmallStep.twp_store32 (address := out) (offset := 0)
    w0 ho0.1 ho0.2.1 ho0.2.2.1 ho0.2.2.2 with Hw0
  isimp only [UInt32.add_zero] at Hw0
  -- the answer
  ihave Hopt : Table.optionU32At 0 out o $$ [Hw0 Hw1]
  · iapply Table.optionU32At_of_words 0 out o payload hpayload
    isplitl_exact Hw0
    · iexact Hw1
  ihave Hnew := Hback $$ Hd0 Hd1 Hd2 Hd3
  ihave Hslice : Slices.ByteSlice 0 map
      (u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes k0 ++ u64Bytes k1)))
      $$ [Hv0 Hv1 Hk0 Hk1]
  · iapply cells_as_slice 0 map v0 v1 k0 k1 (by omega)
    isplitl_exact Hv0
    · isplitl_exact Hv1
      · isplitl_exact Hk0
        · iexact Hk1
  isimp only [← ef12] at Hpay
  ihave Hgo := Hcont
    $$ %(u64Bytes v0 ++ (u64Bytes v1 ++ (u64Bytes k0 ++ u64Bytes k1)))
    %(if o.isSome then 1 else 0) %payload
    %(rfl : (u64Bytes v0 ++ (u64Bytes v1
      ++ (u64Bytes k0 ++ u64Bytes k1))).length = 32)
    Hopt Hnew Hslice Htag Hpay
  iexact Hgo

/-! ## The body -/

set_option maxHeartbeats 4000000 in
/-- The `insert` shim.  It forwards to `HashMap::insert` and builds the
40-byte answer of `map_insert`. -/
theorem func3_correct_of [WasmSmallStepGS hlc Universal.State]
    (hins : Func15InsertSpec (hlc := hlc)) : Func3Spec (hlc := hlc) := by
  unfold Func3Spec CallContract callExpr
  intro sp out map key value k0 k1 t outBefore below heapId storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Phi
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hbump, Hstreams, %hfacts,
    Hcont⟩
  obtain ⟨hout40, hwf, hclean, hitems, hbuckets, hgrowth, hspLow,
    houtBound, hmapBound⟩ := hfacts
  have hsize : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsp160 : (160 : Nat) ≤ sp.toNat := by
    rw [insertWrapDepth_eq] at hspLow; exact hspLow
  have h16 : (16 : UInt32) ≤ sp := by
    apply UInt32.le_iff_toNat_le.mpr
    show (16 : UInt32).toNat ≤ sp.toNat
    have h : (16 : UInt32).toNat = 16 := rfl
    omega
  have hframeNat : (sp - 16).toNat = sp.toNat - 16 := by
    rw [UInt32.toNat_sub_of_le sp 16 h16]
    rfl
  have hslot8 : (sp - 16 + 8).toNat = (sp - 16).toNat + 8 := by
    simpa using Slices.byteOffset_toNat (sp - 16) 8 (by omega)
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 6
      Project.RustHashMap.func3Def (by decide) func3_index with Hmodule
  simp [Project.RustHashMap.func3Def, Project.RustHashMap.func3,
    Function.toLocals, Function.numParams]
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_pures [twp_localGet twp_const twp_add]
    rewriting [UInt32.add_comm 8 (sp - 16)]
  wasm_twp_pures [twp_localGet twp_localGet twp_localGet]
  ihave Hsplit := below_split sp below $$ Hbelow
  icases Hsplit with ⟨%hbelowLen, Hlow, Hframe⟩
  icases (slice_split (sp - 16) 8 (below.drop 144)
    (by rw [List.length_drop]; omega)).mp $$ Hframe with
    ⟨HframeLow, HframeSlot⟩
  isimp only [show UInt32.ofNat 8 = (8 : UInt32) from rfl] at HframeSlot
  have hslotLen : ((below.drop 144).drop 8).length = 8 := by
    rw [List.length_drop, List.length_drop]; omega
  have hlowLen : ((below.drop 144).take 8).length = 8 := by
    rw [List.length_take, List.length_drop]; omega
  ihave Hsp' : StackPointer (sp - 16) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  unfold Func15InsertSpec CallContract callExpr at hins
  simp only [List.cons_append, List.nil_append] at hins
  iapply hins (sp := sp - 16) (out := sp - 16 + 8) (mapBase := map)
    (key := key) (value := value) (k0 := k0) (k1 := k1) (t := t)
    (outBefore := (below.drop 144).drop 8) (below := below.take 144)
    (heapId := heapId) (storedCursor := storedCursor)
    (frontier := frontier) (history := history) (input := input)
    (output := output) (raised := raised)
    (callerLocals := {
      params := [.i32 out, .i32 map, .i32 key, .i32 value]
      locals := [.i32 (sp - 16)]
      values := [] })
    (stack := [])
  isplitl [Hmodule Henv]
  · unfold RuntimeContext
    iframe Hmodule Henv
  isplitl_exacts [Hsp' Hlow HframeSlot Hmap Hbump Hstreams]
  isplitl_pureexact (by
    refine ⟨hslotLen, ?_, ?_, hmapBound, hwf, hclean, hitems, hbuckets,
      hgrowth⟩
    · rw [insertFullDepth_eq, hframeNat]; omega
    · rw [hslot8, hframeNat, hsize]; omega)
  isplit
  · iintro %below' %storedCursor' %frontier' %history' Hruntime Hsp
      Hlow Hslot Hmap Hbump Hstreams
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    iapply twp_func3_tail out map (sp - 16) key value k0 k1
      (Table.insert (SipHash.hashU32 k0 k1) t key value).2
      (Table.insert (SipHash.hashU32 k0 k1) t key value).1 outBefore
      hout40 houtBound hmapBound (by rw [hframeNat]; omega)
    isplitl_exacts [Hout Hmap Hslot]
    iintro %mapBytes %tag %payload %hmapLen Hopt Hnew Hmapslice Htag Hpay
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (16 : UInt32) + (sp - 16) = sp by
      rw [UInt32.add_comm, UInt32.sub_add_cancel]]
    isimp only [StackPointer] at Hsp
    wasm_twp_rebind twp_globalSet with Hsp
    iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
    wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
    simp only [List.take_zero, List.nil_append]
    ihave Harray : arrayAt 0 (sp - 16 + 8) [tag, payload] $$ [Htag Hpay]
    · isimp only [arrayAt]
      isplitl_exact Htag
      · isplitl_exact Hpay
        · itrivial
    ihave Hslotbytes : Slices.ByteSlice 0 (sp - 16 + 8)
        (WordCodec.u32le.serialize [tag, payload]) $$ [Harray]
    · iapply FrameCells.ByteSlice_of_cells (sp - 16 + 8) [tag, payload]
        (by rw [hslot8, hframeNat, hsize]; simp; omega)
      iexact Harray
    ihave Hframe : Slices.ByteSlice 0 (sp - 16)
        ((below.drop 144).take 8 ++
          WordCodec.u32le.serialize [tag, payload]) $$
        [HframeLow Hslotbytes]
    · iapply (Slices.ByteSlice_append (α := Universal.State) 0 (sp - 16)
        ((below.drop 144).take 8)
        (WordCodec.u32le.serialize [tag, payload])).mpr
      isplitl_exact HframeLow
      · irw_exact [← show sp - 16 +
            UInt32.ofNat ((below.drop 144).take 8).length = sp - 16 + 8
          from by rw [hlowLen]; rfl] with Hslotbytes
    ihave Hbelow := below_join sp below'
      ((below.drop 144).take 8 ++
        WordCodec.u32le.serialize [tag, payload])
      (by rw [List.length_append, hlowLen,
        WordCodec.u32le_serialize_length]; rfl) $$ [Hlow Hframe]
    · isplitl_exact Hlow
      · iexact Hframe
    ihave Hsp' : StackPointer sp $$ [Hsp]
    · unfold StackPointer
      iexact Hsp
    iclose_map_runtime Hruntime with Hmodule Henv
    ihave Hnormal := BI.and_elim_l $$ Hcont
    isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
    ihave Hnormal := Hnormal $$ %mapBytes
      %(below' ++ ((below.drop 144).take 8 ++
        WordCodec.u32le.serialize [tag, payload]))
      %storedCursor' %frontier' %history'
    iapply Hnormal $$ Hruntime Hsp' Hbelow Hopt Hnew Hmapslice Hbump
      Hstreams %hmapLen
  · iintro %remaining' Hstreams'
    ihave Hoom := BI.and_elim_r $$ Hcont
    iapply Hoom $$ Hstreams'

end Project.RustHashMap.Func3Proof
