import Project.RustHashMap.BodyContracts
import CodeLib.RustStd.HashMap.TableMem

/-!
# The frame of a body, read as word cells

Every body of the `borsh::io::Error::new` chain takes a frame below the
stack pointer and uses it as whole words.
`Project.RustHashMap.BodyContracts.StackBelow` holds that frame as bytes
and carries no alignment fact, so `Wasm.SepLogic.Slices.WordSlice` does
not apply to it.

`Wasm.SepLogic.arrayAt` needs no alignment.  This module turns the byte
view of a frame into `arrayAt` and back, and it focuses one cell for a
load or a store.  Every frame of the chain is a multiple of four bytes,
so one lemma pair covers them all.

The caller passes the frame base as an argument together with the
equation that names it.  Without that the address in every goal reads
`sp - UInt32.ofNat depth`, which no `simp` set reduces.
-/

namespace Project.RustHashMap.FrameCells

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.BodyContracts

/-- Read a byte slice of `4 * count` bytes as `count` word cells.  The word
list is the decoded view of the bytes, and its length comes out with it. -/
theorem ByteSlice_as_cells [WasmHeapGS Universal.State]
    (base : UInt32) (bytes : List UInt8) (count : Nat)
    (hlength : bytes.length = 4 * count) :
    Slices.ByteSlice 0 base bytes ⊢
      iprop(⌜(Slices.decodeWords bytes).length = count⌝ ∗
        arrayAt 0 base (Slices.decodeWords bytes)) := by
  have hdecode :=
    Slices.u32le_serialize_decodeWords_of_length bytes count hlength
  iintro Hbytes
  isplitl_pureexact hdecode.2
  · isimp only [Slices.ByteSlice] at Hbytes
    icases Hbytes with ⟨%_hnowrap, Hbytes⟩
    iapply (Slices.arrayAt_eq_wordCells 0 base (Slices.decodeWords bytes)).mpr
    isimp only [Slices.WordCells, hdecode.1]
    iexact Hbytes

/-- Give the word cells back as a byte slice. -/
theorem ByteSlice_of_cells [WasmHeapGS Universal.State]
    (base : UInt32) (values : List UInt32)
    (hnowrap : base.toNat + 4 * values.length < UInt32.size) :
    arrayAt 0 base values ⊢
      Slices.ByteSlice 0 base (WordCodec.u32le.serialize values) := by
  iintro Harray
  unfold Slices.ByteSlice
  isplitl_pureexact (by rw [WordCodec.u32le_serialize_length]; exact hnowrap)
  · iapply (Slices.arrayAt_eq_wordCells 0 base values).mp
    iexact Harray

/-- Read a slice that holds a known word list back as cells.  This is the
inverse of `ByteSlice_of_cells`, and it needs no length side condition
because the serialized length is determined. -/
theorem cells_of_ByteSlice [WasmHeapGS Universal.State]
    (base : UInt32) (values : List UInt32) :
    Slices.ByteSlice 0 base (WordCodec.u32le.serialize values) ⊢
      arrayAt 0 base values := by
  iintro Hbytes
  isimp only [Slices.ByteSlice] at Hbytes
  icases Hbytes with ⟨%_hnowrap, Hbytes⟩
  iapply (Slices.arrayAt_eq_wordCells 0 base values).mpr
  isimp only [Slices.WordCells]
  iexact Hbytes

/-- Read the frame of a body as `count` word cells. -/
theorem StackBelow_as_cells [WasmHeapGS Universal.State]
    (sp base : UInt32) (depth count : Nat) (below : List UInt8)
    (hdepth : depth = 4 * count)
    (hbase : sp - UInt32.ofNat depth = base) :
    StackBelow sp depth below ⊢
      iprop(⌜(Slices.decodeWords below).length = count⌝ ∗
        arrayAt 0 base (Slices.decodeWords below)) := by
  subst hbase
  iintro Hbelow
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  iapply ByteSlice_as_cells (sp - UInt32.ofNat depth) below count (by omega)
  iexact Hbytes

/-- Give the frame back as bytes. -/
theorem StackBelow_of_cells [WasmHeapGS Universal.State]
    (sp base : UInt32) (depth count : Nat) (values : List UInt32)
    (hdepth : depth = 4 * count) (hcount : values.length = count)
    (hbase : sp - UInt32.ofNat depth = base)
    (hnowrap : base.toNat + depth < UInt32.size) :
    arrayAt 0 base values ⊢
      StackBelow sp depth (WordCodec.u32le.serialize values) := by
  subst hbase
  have hlen : (WordCodec.u32le.serialize values).length = depth := by
    rw [WordCodec.u32le_serialize_length, hcount, hdepth]
  iintro Harray
  unfold StackBelow
  isplitl_pureexact hlen
  · iapply ByteSlice_of_cells (sp - UInt32.ofNat depth) values
      (by rw [hcount, ← hdepth]; exact hnowrap)
    iexact Harray

/-- Focus one cell of the frame for a load or a store.  The caller names
the byte offset and the old value, so the goals stay free of `getElem` and
of `UInt32.ofNat`.  Both side conditions close by `decide`. -/
theorem cell_focus [WasmHeapGS Universal.State]
    (base offset : UInt32) (values : List UInt32) (k : Nat)
    (old newValue : UInt32)
    (hk : k < values.length) (hold : values[k] = old)
    (hoffset : 4 * UInt32.ofNat k = offset) :
    arrayAt 0 base values ⊢
      iprop(pointsTo_u32 0 (base + offset) old ∗
        (pointsTo_u32 0 (base + offset) newValue -∗
          arrayAt 0 base (values.set k newValue))) := by
  subst hoffset
  subst hold
  exact arrayAt_set 0 base values k newValue hk

/-- Focus one cell of the frame for a load.  The cell comes back
unchanged. -/
theorem cell_load [WasmHeapGS Universal.State]
    (base offset : UInt32) (values : List UInt32) (k : Nat) (old : UInt32)
    (hk : k < values.length) (hold : values[k] = old)
    (hoffset : 4 * UInt32.ofNat k = offset) :
    arrayAt 0 base values ⊢
      iprop(pointsTo_u32 0 (base + offset) old ∗
        (pointsTo_u32 0 (base + offset) old -∗ arrayAt 0 base values)) := by
  subst hoffset
  subst hold
  exact arrayAt_get 0 base values k hk

/-- A two-word slot that both words are written to holds exactly the two
new words.  The eight-byte output slot of a body needs this. -/
theorem set_two (values : List UInt32) (first second : UInt32)
    (hlength : values.length = 2) :
    (values.set 1 second).set 0 first = [first, second] := by
  rcases values with _ | ⟨x, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨y, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨z, rest⟩
  · rfl
  · simp at hlength

/-- The three-word output slot after the three stores that fill it. -/
theorem set_three (values : List UInt32) (first second third : UInt32)
    (hlength : values.length = 3) :
    ((values.set 1 second).set 2 third).set 0 first = [first, second, third] := by
  rcases values with _ | ⟨x, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨y, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨z, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨w, rest⟩
  · rfl
  · simp at hlength

/-- The four address facts that `twp_load32` and `twp_store32` ask for at
one frame offset. -/
theorem offset_facts (base offset : UInt32) (o : Nat)
    (hoffset : UInt32.ofNat o = offset)
    (hbound : base.toNat + o + 4 ≤ UInt32.size) :
    (base + offset).toNat = base.toNat + offset.toNat ∧
      (base + offset + 1).toNat = (base + offset).toNat + 1 ∧
      (base + offset + 2).toNat = (base + offset).toNat + 2 ∧
      (base + offset + 3).toNat = (base + offset).toNat + 3 := by
  subst hoffset
  have ho : o < UInt32.size := by omega
  have hto : (UInt32.ofNat o).toNat = o := UInt32.toNat_ofNat_of_lt' ho
  have h0 : (base + UInt32.ofNat o).toNat = base.toNat + o :=
    Slices.byteOffset_toNat base o (by omega)
  refine ⟨by rw [h0, hto], ?_, ?_, ?_⟩
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)

/-- The three-word output slot of the `String` builder.  The body writes
the third cell twice, so the dead value falls out. -/
theorem set_three_twice (values : List UInt32) (first second third : UInt32)
    (hlength : values.length = 3) :
    ((((values.set 0 first).set 1 second).set 2 0).set 2 third)
      = [first, second, third] := by
  rcases values with _ | ⟨x, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨y, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨z, rest⟩
  · simp at hlength
  rcases rest with _ | ⟨w, rest⟩
  · rfl
  · simp at hlength

/-- The eight address facts that `twp_load64` and `twp_store64` ask for
at one frame offset. -/
theorem offset_facts64 (base offset : UInt32) (o : Nat)
    (hoffset : UInt32.ofNat o = offset)
    (hbound : base.toNat + o + 8 ≤ UInt32.size) :
    (base + offset).toNat = base.toNat + offset.toNat ∧
      (base + offset + 1).toNat = (base + offset).toNat + 1 ∧
      (base + offset + 2).toNat = (base + offset).toNat + 2 ∧
      (base + offset + 3).toNat = (base + offset).toNat + 3 ∧
      (base + offset + 4).toNat = (base + offset).toNat + 4 ∧
      (base + offset + 5).toNat = (base + offset).toNat + 5 ∧
      (base + offset + 6).toNat = (base + offset).toNat + 6 ∧
      (base + offset + 7).toNat = (base + offset).toNat + 7 := by
  subst hoffset
  have ho : o < UInt32.size := by omega
  have hto : (UInt32.ofNat o).toNat = o := UInt32.toNat_ofNat_of_lt' ho
  have h0 : (base + UInt32.ofNat o).toNat = base.toNat + o :=
    Slices.byteOffset_toNat base o (by omega)
  refine ⟨by rw [h0, hto], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 1 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 2 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 3 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 4 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 5 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 6 (by omega)
  · simpa using Slices.byteOffset_toNat (base + UInt32.ofNat o) 7 (by omega)

/-! ## The own frame and the region that a callee gets -/

/-- Lowering an address twice is one subtraction. -/
theorem sub_sub_ofNat (sp : UInt32) (a b : Nat) :
    sp - UInt32.ofNat a - UInt32.ofNat b = sp - UInt32.ofNat (a + b) := by
  apply UInt32.eq_of_toBitVec_eq
  simp only [UInt32.toBitVec_sub]
  rw [BitVec.sub_sub]
  congr 1
  rw [← UInt32.toBitVec_add, ← UInt32.ofNat_add]

/-- The base of the whole region, read through the frame pointer. -/
theorem frame_base (sp : UInt32) (deep own : Nat) (hle : own ≤ deep) :
    sp - UInt32.ofNat own - UInt32.ofNat (deep - own) = sp - UInt32.ofNat deep := by
  rw [sub_sub_ofNat, show own + (deep - own) = deep from by omega]

/-- The frame pointer, read through the base of the whole region. -/
theorem frame_top (sp : UInt32) (deep own : Nat) (hle : own ≤ deep) :
    sp - UInt32.ofNat own
      = sp - UInt32.ofNat deep + UInt32.ofNat (deep - own) := by
  rw [← frame_base sp deep own hle, UInt32.sub_add_cancel]

/-- Cut the own frame off the top of the stack region.  The callee gets the
deeper part under the lowered stack pointer, and the caller keeps the `own`
bytes directly below its own stack pointer. -/
theorem frame_split [WasmHeapGS Universal.State]
    (sp : UInt32) (deep own : Nat) (bytes : List UInt8)
    (hle : own ≤ deep) :
    StackBelow sp deep bytes ⊢
      iprop(StackBelow (sp - UInt32.ofNat own) (deep - own)
          (bytes.take (deep - own)) ∗
        StackBelow sp own (bytes.drop (deep - own))) := by
  have hbase := frame_base sp deep own hle
  have hframe := frame_top sp deep own hle
  iintro Hbelow
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  have hsplit : bytes.take (deep - own) ++ bytes.drop (deep - own) = bytes :=
    List.take_append_drop _ _
  have htakeLength : (bytes.take (deep - own)).length = deep - own := by
    rw [List.length_take, hlength]
    omega
  ihave ⟨Hlow, Hhigh⟩ :=
    (Slices.ByteSlice_append 0 (sp - UInt32.ofNat deep)
      (bytes.take (deep - own)) (bytes.drop (deep - own))).mp $$ [Hbytes]
  · irw_exact [hsplit] with Hbytes
  isplitl [Hlow]
  · isplitl_pureexact htakeLength
    irw_exact [hbase] with Hlow
  isplitl_pureexact (by rw [List.length_drop, hlength]; omega)
  irw_exact [hframe, htakeLength] with Hhigh

/-- Put the stack region back together after the callee returns. -/
theorem frame_join [WasmHeapGS Universal.State]
    (sp : UInt32) (deep own : Nat) (low high : List UInt8)
    (hlow : low.length = deep - own)
    (hle : own ≤ deep) :
    iprop(StackBelow (sp - UInt32.ofNat own) (deep - own) low ∗
        StackBelow sp own high) ⊢
      StackBelow sp deep (low ++ high) := by
  have hbase := frame_base sp deep own hle
  have hframe := frame_top sp deep own hle
  iintro ⟨Hlow, Hhigh⟩
  unfold StackBelow
  icases Hlow with ⟨%_hlowLength, Hlow⟩
  icases Hhigh with ⟨%hhighLength, Hhigh⟩
  isplitl_pureexact (by rw [List.length_append, hlow, hhighLength]; omega)
  iapply (Slices.ByteSlice_append 0 (sp - UInt32.ofNat deep) low high).mpr
  isplitl [Hlow]
  · irw_exact [← hbase] with Hlow
  irw_exact [hlow, ← hframe] with Hhigh

/-! ## Cutting a slot out of the own frame -/

/-- A `StackBelow` region is a slice at its base address. -/
theorem StackBelow_base [WasmHeapGS Universal.State]
    (sp base : UInt32) (depth : Nat) (bytes : List UInt8)
    (hbase : sp - UInt32.ofNat depth = base) :
    StackBelow sp depth bytes ⊢
      iprop(⌜bytes.length = depth⌝ ∗ Slices.ByteSlice 0 base bytes) := by
  subst hbase
  iintro Hbelow
  unfold StackBelow
  iexact Hbelow

/-- A slice of the right length at the base address is a `StackBelow`
region. -/
theorem StackBelow_intro [WasmHeapGS Universal.State]
    (sp base : UInt32) (depth : Nat) (bytes : List UInt8)
    (hlength : bytes.length = depth)
    (hbase : sp - UInt32.ofNat depth = base) :
    Slices.ByteSlice 0 base bytes ⊢ StackBelow sp depth bytes := by
  subst hbase
  iintro Hbytes
  unfold StackBelow
  isplitl_pureexact hlength
  iexact Hbytes

/-- Cut a slice at a byte offset.  The frame of a body holds the output
slot of its callee at a fixed offset, and this names it. -/
theorem ByteSlice_cut [WasmHeapGS Universal.State]
    (base : UInt32) (bytes : List UInt8) (k : Nat) (hk : k ≤ bytes.length) :
    Slices.ByteSlice 0 base bytes ⊢
      iprop(Slices.ByteSlice 0 base (bytes.take k) ∗
        Slices.ByteSlice 0 (base + UInt32.ofNat k) (bytes.drop k)) := by
  have hsplit : bytes.take k ++ bytes.drop k = bytes := List.take_append_drop _ _
  have hlen : (bytes.take k).length = k := by rw [List.length_take]; omega
  have haddr : base + UInt32.ofNat (bytes.take k).length
      = base + UInt32.ofNat k := by rw [hlen]
  iintro Hbytes
  ihave ⟨Hlow, Hhigh⟩ :=
    (Slices.ByteSlice_append 0 base (bytes.take k) (bytes.drop k)).mp $$ [Hbytes]
  · irw_exact [hsplit] with Hbytes
  isplitl_exact Hlow
  · irw_exact [← haddr] with Hhigh

/-- Put a cut slice back together. -/
theorem ByteSlice_glue [WasmHeapGS Universal.State]
    (base : UInt32) (low high : List UInt8) (k : Nat) (hlow : low.length = k) :
    iprop(Slices.ByteSlice 0 base low ∗
        Slices.ByteSlice 0 (base + UInt32.ofNat k) high) ⊢
      Slices.ByteSlice 0 base (low ++ high) := by
  iintro ⟨Hlow, Hhigh⟩
  iapply (Slices.ByteSlice_append 0 base low high).mpr
  isplitl_exact Hlow
  · irw_exact [hlow] with Hhigh

/-- Read the length of a stack region without giving it up. -/
theorem StackBelow_length [WasmHeapGS Universal.State]
    (sp : UInt32) (depth : Nat) (bytes : List UInt8) :
    StackBelow sp depth bytes ⊢
      iprop(StackBelow sp depth bytes ∗ ⌜bytes.length = depth⌝) := by
  iintro Hbelow
  unfold StackBelow
  icases Hbelow with ⟨%hlength, Hbytes⟩
  isplitl [Hbytes]
  · isplitl_pureexact hlength
    iexact Hbytes
  · ipureexact hlength

/-- Two offsets from the same base add. -/
theorem frame_offset (base : UInt32) (lo hi total : Nat)
    (htotal : lo + hi = total) :
    base + UInt32.ofNat lo + UInt32.ofNat hi
      = base + UInt32.ofNat total := by
  rw [UInt32.add_assoc, ← UInt32.ofNat_add, htotal]

/-! ## Eight-byte block moves

A compiled block move is two `local.get`s, one `i64.load`, and one
`i64.store`.  The two memory rules take one owned `pointsTo_u64` at the
address that each rule computes.  The bytes of a frame or of an output
slot arrive as `Slices.ByteSlice`, so every move needs one wrap and one
unwrap.

The pair below does that.  It hides the bound that
`Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64` returns beside the
word, and it takes the address equation as an argument.  A rule with the
offset 0 asks for the word at `base + 0` while the slice sits at `base`,
so the caller passes `hbaseZero : base + 0 = base` there and `rfl`
everywhere else. -/

/-- Eight owned bytes as the group word that the `i64` rules take. -/
theorem ByteSlice_as_word [WasmHeapGS Universal.State]
    (addr target : UInt32) (bytes : List UInt8)
    (haddr : target = addr) (hlength : bytes.length = 8) :
    Slices.ByteSlice 0 addr bytes ⊢
      pointsTo_u64 0 target (Wasm.RustStd.HashMap.Table.groupWord bytes) := by
  subst haddr
  iintro Hbytes
  ihave ⟨%_hbound, Hword⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 target bytes
      hlength).mp $$ Hbytes
  iexact Hword

/-- The group word back as eight owned bytes. -/
theorem ByteSlice_of_word [WasmHeapGS Universal.State]
    (addr target : UInt32) (bytes : List UInt8)
    (haddr : target = addr) (hlength : bytes.length = 8)
    (hbound : addr.toNat + 8 < UInt32.size) :
    pointsTo_u64 0 target (Wasm.RustStd.HashMap.Table.groupWord bytes) ⊢
      Slices.ByteSlice 0 addr bytes := by
  subst haddr
  iintro Hword
  iapply (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 target bytes
    hlength).mpr
  isplitl_pureexact hbound
  iexact Hword

/-- Run one eight-byte block move.  The two address bundles come from
`offset_facts64` and stay undestructured, so each move names two
hypotheses instead of sixteen. -/
macro "wasm_twp_block_move "
    "(" src:term ", " soff:term ", " srcWord:term ", " hsrc:term ")"
    "(" dst:term ", " doff:term ", " dstWord:term ", " hdst:term ")"
    " with " srcRes:ident dstRes:ident : tactic =>
  `(tactic|
    (wasm_twp_pures [twp_localGet twp_localGet]
     wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := $src)
       (offset := $soff) $srcWord
       ($hsrc).1 ($hsrc).2.1 ($hsrc).2.2.1 ($hsrc).2.2.2.1
       ($hsrc).2.2.2.2.1 ($hsrc).2.2.2.2.2.1 ($hsrc).2.2.2.2.2.2.1
       ($hsrc).2.2.2.2.2.2.2 with $srcRes
     wasm_twp_rebind Wasm.SmallStep.twp_store64 (address := $dst)
       (offset := $doff) $dstWord
       ($hdst).1 ($hdst).2.1 ($hdst).2.2.1 ($hdst).2.2.2.1
       ($hdst).2.2.2.2.1 ($hdst).2.2.2.2.2.1 ($hdst).2.2.2.2.2.2.1
       ($hdst).2.2.2.2.2.2.2 with $dstRes))

/-! ## Word blocks of a record -/

/-- Three encoded words, as a two-word block and a one-word block.  A
precondition carries the record as three `encode` blocks, and the two
`i64` moves of a pack take it as two `serialize` blocks. -/
theorem encode_three_as_two_one (a b c : UInt32) :
    WordCodec.u32le.encode a
        ++ (WordCodec.u32le.encode b ++ WordCodec.u32le.encode c)
      = WordCodec.u32le.serialize [a, b] ++ WordCodec.u32le.serialize [c] := by
  simp [WordCodec.serialize_cons, WordCodec.serialize_nil, List.append_assoc]

/-- Normalize the serialized word blocks of a slot that a body rebuilt.
The blocks arrive as one `serialize` call for each `i64` or `i32` store,
and a postcondition asks for one `serialize` call over the whole word
list. -/
macro "wasm_serialize_norm" " at " target:ident : tactic =>
  `(tactic|
    isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_nil, List.append_assoc] at $target:ident)

end Project.RustHashMap.FrameCells
