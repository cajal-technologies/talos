import Project.RustHashMap.ErrorNewContracts
import Project.RustHashMap.FrameCells
import CodeLib.RustStd.HashMap.TableMem

/-!
# Proof of the pack of the `io::Error::new` chain

Local `func53` (absolute index 56) packs the twelve-byte record and the
`ErrorKind` byte into the sixteen-byte slot of its caller.  It calls
nothing.

Three things make this body different from the rest of the chain.

The frame is a red zone.  The body computes `local 3 := sp - 32` and
never writes the stack pointer, so the 32 bytes are borrowed from
`StackBelow sp func53Depth below`, written, and given back as `below'`.
The postcondition quantifies `below'`, so nothing above cares what stays
there.

The body writes the kind with `i32.store8`, the only `store8` of the
chain.  The rule takes one owned byte, so the proof cuts that byte out of
the frame with `Slices.ByteSlice_singleton`, below the word view.

The body then runs three `i64` shuffles.  Each one is an opaque
eight-byte block move through
`Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64`, so no bitvector
tactic runs.

Word 3 of the output stays abstract.  The body reads the whole word back
at `frame + 24`, and its top three bytes are red-zone bytes that the
caller left there.  The proof names that word through the decoded view of
four bytes and never computes it.

The proof puts every `omega` goal in front of the address facts.  Each
`offset_facts64` adds eight `UInt32.toNat` equations to the context, and
`omega` reads the whole context, so an `omega` after the address facts
costs more than ten seconds.  Every side condition here carries a name
and gets proved while the context is still small.
-/

namespace Project.RustHashMap.Func53Proof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.ErrorNewContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

private theorem func53_index :
    Project.RustHashMap.«module».funcs[53]? =
      some Project.RustHashMap.func53Def := by rfl

set_option maxHeartbeats 2000000 in
theorem func53_correct [WasmSmallStepGS hlc Universal.State] :
    Func53Spec (hlc := hlc) := by
  unfold Func53Spec CallContract callExpr
  intro sp out kind record word0 word1 word2 outBefore below callerLocals
    stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hrecord, %hfacts, Hcont⟩
  obtain ⟨houtLength, hspLow, houtNowrap, hrecNowrap⟩ := hfacts
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 56
      Project.RustHashMap.func53Def (by decide) func53_index with Hmodule
  simp [Project.RustHashMap.func53Def, Project.RustHashMap.func53,
    Function.toLocals, Function.numParams]
  -- arithmetic on the red-zone base
  have hdepth53 : func53Depth = 32 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspNat : (32 : Nat) ≤ sp.toNat := by rw [hdepth53] at hspLow; exact hspLow
  have hframeNat : (sp - 32).toNat = sp.toNat - 32 := by
    rw [UInt32.toNat_sub_of_le sp 32
      (UInt32.le_iff_toNat_le.mpr (by simpa using (by omega : (32 : Nat) ≤ sp.toNat)))]
    rfl
  have hbase32 : sp - UInt32.ofNat func53Depth = sp - 32 := by
    rw [show UInt32.ofNat func53Depth = 32 from by decide]
  have hf8 : sp - 32 + UInt32.ofNat 8 = sp - 32 + 8 := rfl
  have hf16 : sp - 32 + (8 : UInt32) + UInt32.ofNat 8 = sp - 32 + 16 :=
    frame_offset (sp - 32) 8 8 16 rfl
  have hf24 : sp - 32 + (16 : UInt32) + UInt32.ofNat 8 = sp - 32 + 24 :=
    frame_offset (sp - 32) 16 8 24 rfl
  have hf28 : sp - 32 + (24 : UInt32) + UInt32.ofNat 4 = sp - 32 + 28 :=
    frame_offset (sp - 32) 24 4 28 rfl
  have hf29 : sp - 32 + (28 : UInt32) + UInt32.ofNat 1 = sp - 32 + 29 :=
    frame_offset (sp - 32) 28 1 29 rfl
  have hf8Nat : (sp - 32 + (8 : UInt32)).toNat = (sp - 32).toNat + 8 :=
    Slices.byteOffset_toNat (sp - 32) 8 (by omega)
  have hf16Nat : (sp - 32 + (16 : UInt32)).toNat = (sp - 32).toNat + 16 :=
    Slices.byteOffset_toNat (sp - 32) 16 (by omega)
  have hf24Nat : (sp - 32 + (24 : UInt32)).toNat = (sp - 32).toNat + 24 :=
    Slices.byteOffset_toNat (sp - 32) 24 (by omega)
  have hf28Nat : (sp - 32 + (28 : UInt32)).toNat = (sp - 32).toNat + 28 :=
    Slices.byteOffset_toNat (sp - 32) 28 (by omega)
  have hs28 : (sp - 32 + (28 : UInt32)).toNat
      = (sp - 32).toNat + (28 : UInt32).toNat := by rw [hf28Nat]; rfl
  have hfZero : sp - 32 + (0 : UInt32) = sp - 32 := by simp
  have houtZero : out + (0 : UInt32) = out := by simp
  have hrecZero : record + (0 : UInt32) = record := by simp
  have hout8 : out + UInt32.ofNat 8 = out + 8 := rfl
  have hout12 : out + (8 : UInt32) + UInt32.ofNat 4 = out + 12 :=
    frame_offset out 8 4 12 rfl
  have hout8Nat : (out + (8 : UInt32)).toNat = out.toNat + 8 :=
    Slices.byteOffset_toNat out 8 (by omega)
  have hout12Nat : (out + (12 : UInt32)).toNat = out.toNat + 12 :=
    Slices.byteOffset_toNat out 12 (by omega)
  have hrec8 : record + UInt32.ofNat 8 = record + 8 := rfl
  have hrec8Nat : (record + (8 : UInt32)).toNat = record.toNat + 8 :=
    Slices.byteOffset_toNat record 8 (by omega)
  -- the record splits into an eight-byte block and the third word
  have hrecLow8 : (WordCodec.u32le.serialize [word0, word1]).length = 8 := by simp
  have hw2Length : (WordCodec.u32le.serialize [word2]).length = 4 := by simp
  have hrecSplit : WordCodec.u32le.encode word0
      ++ (WordCodec.u32le.encode word1 ++ WordCodec.u32le.encode word2)
      = WordCodec.u32le.serialize [word0, word1]
        ++ WordCodec.u32le.serialize [word2] := by
    simp [WordCodec.serialize_cons, WordCodec.serialize_nil,
      List.append_assoc]
  ihave ⟨Hreclow, Hrechigh⟩ :=
    (Slices.ByteSlice_append 0 record (WordCodec.u32le.serialize [word0, word1])
      (WordCodec.u32le.serialize [word2])).mp $$ [Hrecord]
  · irw_exact [← hrecSplit] with Hrecord
  isimp only [hrecLow8, hrec8] at Hrechigh
  -- the caller's output slot splits into two eight-byte blocks
  ihave ⟨Houtlow, Houthigh⟩ := ByteSlice_cut out outBefore 8 (by omega) $$ Hout
  isimp only [hout8] at Houthigh
  have houtLow8 : (outBefore.take 8).length = 8 := by simp [houtLength]
  have houtHigh8 : (outBefore.drop 8).length = 8 := by
    rw [List.length_drop, houtLength]
  set outlow := outBefore.take 8 with houtlowDef
  set outhigh := outBefore.drop 8 with houthighDef
  -- the red zone splits into four eight-byte blocks
  ihave ⟨%hbelowLength, Hframe⟩ :=
    StackBelow_base sp (sp - 32) func53Depth below hbase32 $$ Hbelow
  have hbelowLen : below.length = 32 := by rw [hbelowLength, hdepth53]
  ihave ⟨Hb0, Hrest1⟩ := ByteSlice_cut (sp - 32) below 8 (by omega) $$ Hframe
  isimp only [hf8] at Hrest1
  have hb0Length : (below.take 8).length = 8 := by simp [hbelowLen]
  have hrest1Length : (below.drop 8).length = 24 := by
    rw [List.length_drop, hbelowLen]
  set b0 := below.take 8 with hb0Def
  set rest1 := below.drop 8 with hrest1Def
  ihave ⟨Hb1, Hrest2⟩ :=
    ByteSlice_cut (sp - 32 + 8) rest1 8 (by omega) $$ Hrest1
  isimp only [hf16] at Hrest2
  have hb1Length : (rest1.take 8).length = 8 := by simp [hrest1Length]
  have hrest2Length : (rest1.drop 8).length = 16 := by
    rw [List.length_drop, hrest1Length]
  set b1 := rest1.take 8 with hb1Def
  set rest2 := rest1.drop 8 with hrest2Def
  ihave ⟨Hb2, Hb3⟩ :=
    ByteSlice_cut (sp - 32 + 16) rest2 8 (by omega) $$ Hrest2
  isimp only [hf24] at Hb3
  have hb2Length : (rest2.take 8).length = 8 := by simp [hrest2Length]
  have hb3Length : (rest2.drop 8).length = 8 := by
    rw [List.length_drop, hrest2Length]
  set b2 := rest2.take 8 with hb2Def
  set b3 := rest2.drop 8 with hb3Def
  -- the fourth block splits into the word slot, the kind byte, and padding
  ihave ⟨Hb3low, Hb3high⟩ :=
    ByteSlice_cut (sp - 32 + 24) b3 4 (by omega) $$ Hb3
  isimp only [hf28] at Hb3high
  have hb3lowLength : (b3.take 4).length = 4 := by simp [hb3Length]
  have hb3highLength : (b3.drop 4).length = 4 := by
    rw [List.length_drop, hb3Length]
  set b3low := b3.take 4 with hb3lowDef
  set b3high := b3.drop 4 with hb3highDef
  ihave ⟨Hkind, Hpad⟩ :=
    ByteSlice_cut (sp - 32 + 28) b3high 1 (by omega) $$ Hb3high
  isimp only [hf29] at Hpad
  have hkindLength : (b3high.take 1).length = 1 := by simp [hb3highLength]
  have hpadLength : (b3high.drop 1).length = 3 := by
    rw [List.length_drop, hb3highLength]
  set pad := b3high.drop 1 with hpadDef
  have hg3Length : (WordCodec.u32le.serialize [word2]
      ++ ([kind.toUInt8] ++ pad)).length = 8 := by simp [hpadLength]
  obtain ⟨oldKindByte, hkindShape⟩ := List.length_eq_one_iff.mp hkindLength
  isimp only [hkindShape] at Hkind
  ihave ⟨%_hkindBound, Hkindbyte⟩ :=
    (Slices.ByteSlice_singleton 0 (sp - 32 + 28) oldKindByte).mp $$ Hkind
  -- every remaining side condition, named while the context is still small
  have hcellsF24 : b3low.length = 4 * 1 := by omega
  have hcellsO12 : ([kind.toUInt8] ++ pad).length = 4 * 1 := by
    simp [hpadLength]
  have hsingle28 : (sp - 32 + 28).toNat + 1 < UInt32.size := by
    rw [hf28Nat]; omega
  have hwordF0 : (sp - 32).toNat + 8 < UInt32.size := by omega
  have hwordF8 : (sp - 32 + 8).toNat + 8 < UInt32.size := by
    rw [hf8Nat]; omega
  have hwordF16 : (sp - 32 + 16).toNat + 8 < UInt32.size := by
    rw [hf16Nat]; omega
  have hwordF24 : (sp - 32 + 24).toNat + 8 < UInt32.size := by
    rw [hf24Nat]; omega
  have hwordR0 : record.toNat + 8 < UInt32.size := by omega
  have hwordO0 : out.toNat + 8 < UInt32.size := by omega
  have hwordO8 : (out + 8).toNat + 8 < UInt32.size := by
    rw [hout8Nat]; omega
  have hofcF24 : (sp - 32 + 24).toNat
      + 4 * ([word2] : List UInt32).length < UInt32.size := by
    simp only [List.length_cons, List.length_nil]
    rw [hf24Nat]; omega
  have hofcR8 : (record + 8).toNat
      + 4 * ([word2] : List UInt32).length < UInt32.size := by
    simp only [List.length_cons, List.length_nil]
    rw [hrec8Nat]; omega
  have hofcO12 : ∀ w : UInt32, (out + 12).toNat
      + 4 * ([w] : List UInt32).length < UInt32.size := by
    intro w
    simp only [List.length_cons, List.length_nil]
    rw [hout12Nat]; omega
  have hboundF0 : (sp - 32).toNat + 0 + 8 ≤ UInt32.size := by omega
  have hboundF8 : (sp - 32).toNat + 8 + 8 ≤ UInt32.size := by omega
  have hboundF16 : (sp - 32).toNat + 16 + 8 ≤ UInt32.size := by omega
  have hboundF24 : (sp - 32).toNat + 24 + 8 ≤ UInt32.size := by omega
  have hboundF24w : (sp - 32).toNat + 24 + 4 ≤ UInt32.size := by omega
  have hboundR0 : record.toNat + 0 + 8 ≤ UInt32.size := by omega
  have hboundR8 : record.toNat + 8 + 4 ≤ UInt32.size := by omega
  have hboundO0 : out.toNat + 0 + 8 ≤ UInt32.size := by omega
  have hboundO8 : out.toNat + 8 + 8 ≤ UInt32.size := by omega
  -- the address facts of every access
  obtain ⟨hf0a, hf0b, hf0c, hf0d, hf0e, hf0f, hf0g, hf0h⟩ :=
    offset_facts64 (sp - 32) 0 0 rfl hboundF0
  obtain ⟨hf8a, hf8b, hf8c, hf8d, hf8e, hf8f, hf8g, hf8h⟩ :=
    offset_facts64 (sp - 32) 8 8 rfl hboundF8
  obtain ⟨hf16a, hf16b, hf16c, hf16d, hf16e, hf16f, hf16g, hf16h⟩ :=
    offset_facts64 (sp - 32) 16 16 rfl hboundF16
  obtain ⟨hf24a, hf24b, hf24c, hf24d, hf24e, hf24f, hf24g, hf24h⟩ :=
    offset_facts64 (sp - 32) 24 24 rfl hboundF24
  obtain ⟨hf24w, hf24w1, hf24w2, hf24w3⟩ :=
    offset_facts (sp - 32) 24 24 rfl hboundF24w
  obtain ⟨hr0a, hr0b, hr0c, hr0d, hr0e, hr0f, hr0g, hr0h⟩ :=
    offset_facts64 record 0 0 rfl hboundR0
  obtain ⟨hr8w, hr8w1, hr8w2, hr8w3⟩ :=
    offset_facts record 8 8 rfl hboundR8
  obtain ⟨ho0a, ho0b, ho0c, ho0d, ho0e, ho0f, ho0g, ho0h⟩ :=
    offset_facts64 out 0 0 rfl hboundO0
  obtain ⟨ho8a, ho8b, ho8c, ho8d, ho8e, ho8f, ho8g, ho8h⟩ :=
    offset_facts64 out 8 8 rfl hboundO8
  -- `local 3 := sp - 32`
  isimp only [StackPointer] at Hsp
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  -- `[frame + 28] := kind` as one byte
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store8 (address := sp - 32) (offset := 28) oldKindByte
    hs28 with Hkindbyte
  -- `[frame + 24] := [record + 8]`
  ihave Hreccells := cells_of_ByteSlice (record + 8) [word2] $$ Hrechigh
  isimp only [arrayAt] at Hreccells
  icases Hreccells with ⟨Hreccell, _Hrecnil⟩
  ihave ⟨%hb3lowCells, Hb3lowarray⟩ :=
    ByteSlice_as_cells (sp - 32 + 24) b3low 1 hcellsF24 $$ Hb3low
  obtain ⟨oldWord6, hb3lowShape⟩ := List.length_eq_one_iff.mp hb3lowCells
  isimp only [hb3lowShape, arrayAt] at Hb3lowarray
  icases Hb3lowarray with ⟨Hb3lowcell, _Hb3lownil⟩
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := record) (offset := 8) word2
    hr8w hr8w1 hr8w2 hr8w3 with Hreccell
  wasm_twp_rebind twp_store32 (address := sp - 32) (offset := 24) oldWord6
    hf24w hf24w1 hf24w2 hf24w3 with Hb3lowcell
  -- `[frame + 16 .. 24] := [record + 0 .. 8]`, a block move
  ihave ⟨%_hrecwordBound, Hrecword⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 record
      (WordCodec.u32le.serialize [word0, word1]) hrecLow8).mp $$ Hreclow
  ihave Hrecword :
      pointsTo_u64 0 (record + 0)
        (Wasm.RustStd.HashMap.Table.groupWord
          (WordCodec.u32le.serialize [word0, word1])) $$ [Hrecword]
  · irw_exact [hrecZero] with Hrecword
  ihave ⟨%_hb2Bound, Hb2word⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32 + 16)
      b2 hb2Length).mp $$ Hb2
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load64 (address := record) (offset := 0)
    (Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [word0, word1]))
    hr0a hr0b hr0c hr0d hr0e hr0f hr0g hr0h with Hrecword
  wasm_twp_rebind twp_store64 (address := sp - 32) (offset := 16)
    (Wasm.RustStd.HashMap.Table.groupWord b2)
    hf16a hf16b hf16c hf16d hf16e hf16f hf16g hf16h with Hb2word
  -- rebuild the fourth block: the word, the kind byte, and the padding
  ihave Hb3lowarray : arrayAt 0 (sp - 32 + 24) [word2] $$ [Hb3lowcell]
  · isimp only [arrayAt]
    iframe Hb3lowcell
  ihave Hb3low :=
    ByteSlice_of_cells (sp - 32 + 24) [word2] hofcF24 $$ Hb3lowarray
  ihave Hkind :=
    (Slices.ByteSlice_singleton 0 (sp - 32 + 28) kind.toUInt8).mpr $$
      [Hkindbyte]
  · isplitl_pureexact hsingle28
    iexact Hkindbyte
  ihave Hb3high :=
    ByteSlice_glue (sp - 32 + 28) [kind.toUInt8] pad 1 rfl $$ [Hkind Hpad]
  · isplitl_exact Hkind
    · irw_exact [hf29] with Hpad
  ihave Hb3 :=
    ByteSlice_glue (sp - 32 + 24) (WordCodec.u32le.serialize [word2])
      ([kind.toUInt8] ++ pad) 4 hw2Length $$ [Hb3low Hb3high]
  · isplitl_exact Hb3low
    · irw_exact [hf28] with Hb3high
  ihave ⟨%_hb3Bound, Hb3word⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32 + 24)
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
      hg3Length).mp $$ Hb3
  -- `[frame + 8 .. 16] := [frame + 24 .. 32]`, a block move
  ihave ⟨%_hb1Bound, Hb1word⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32 + 8)
      b1 hb1Length).mp $$ Hb1
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load64 (address := sp - 32) (offset := 24)
    (Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad)))
    hf24a hf24b hf24c hf24d hf24e hf24f hf24g hf24h with Hb3word
  wasm_twp_rebind twp_store64 (address := sp - 32) (offset := 8)
    (Wasm.RustStd.HashMap.Table.groupWord b1)
    hf8a hf8b hf8c hf8d hf8e hf8f hf8g hf8h with Hb1word
  -- `[frame + 0 .. 8] := [frame + 16 .. 24]`, a block move
  ihave ⟨%_hb0Bound, Hb0word⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32)
      b0 hb0Length).mp $$ Hb0
  ihave Hb0word :
      pointsTo_u64 0 (sp - 32 + 0)
        (Wasm.RustStd.HashMap.Table.groupWord b0) $$ [Hb0word]
  · irw_exact [hfZero] with Hb0word
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load64 (address := sp - 32) (offset := 16)
    (Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [word0, word1]))
    hf16a hf16b hf16c hf16d hf16e hf16f hf16g hf16h with Hb2word
  wasm_twp_rebind twp_store64 (address := sp - 32) (offset := 0)
    (Wasm.RustStd.HashMap.Table.groupWord b0)
    hf0a hf0b hf0c hf0d hf0e hf0f hf0g hf0h with Hb0word
  -- `[out + 8 .. 16] := [frame + 8 .. 16]`, a block move
  ihave ⟨%_houthighBound, Houthighword⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (out + 8)
      outhigh houtHigh8).mp $$ Houthigh
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load64 (address := sp - 32) (offset := 8)
    (Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad)))
    hf8a hf8b hf8c hf8d hf8e hf8f hf8g hf8h with Hb1word
  wasm_twp_rebind twp_store64 (address := out) (offset := 8)
    (Wasm.RustStd.HashMap.Table.groupWord outhigh)
    ho8a ho8b ho8c ho8d ho8e ho8f ho8g ho8h with Houthighword
  -- `[out + 0 .. 8] := [frame + 0 .. 8]`, a block move
  ihave ⟨%_houtlowBound, Houtlowword⟩ :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 out
      outlow houtLow8).mp $$ Houtlow
  ihave Houtlowword :
      pointsTo_u64 0 (out + 0)
        (Wasm.RustStd.HashMap.Table.groupWord outlow) $$ [Houtlowword]
  · irw_exact [houtZero] with Houtlowword
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load64 (address := sp - 32) (offset := 0)
    (Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [word0, word1]))
    hf0a hf0b hf0c hf0d hf0e hf0f hf0g hf0h with Hb0word
  wasm_twp_rebind twp_store64 (address := out) (offset := 0)
    (Wasm.RustStd.HashMap.Table.groupWord outlow)
    ho0a ho0b ho0c ho0d ho0e ho0f ho0g ho0h with Houtlowword
  wasm_twp_return_from_call Hmodule [List.take_zero, List.nil_append]
  -- the caller's output slot, as bytes again
  isimp only [houtZero] at Houtlowword
  ihave Houtlow :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 out
      (WordCodec.u32le.serialize [word0, word1]) hrecLow8).mpr $$
      [Houtlowword]
  · isplitl_pureexact hwordO0
    iexact Houtlowword
  ihave Houthigh :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (out + 8)
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
      hg3Length).mpr $$ [Houthighword]
  · isplitl_pureexact hwordO8
    iexact Houthighword
  -- the fourth word of the output is the kind byte and three red-zone bytes
  ihave ⟨Houtw2, Houtw3⟩ :=
    (Slices.ByteSlice_append 0 (out + 8) (WordCodec.u32le.serialize [word2])
      ([kind.toUInt8] ++ pad)).mp $$ Houthigh
  isimp only [hw2Length, hout12] at Houtw3
  ihave ⟨%hw3Cells, Houtw3array⟩ :=
    ByteSlice_as_cells (out + 12) ([kind.toUInt8] ++ pad) 1
      hcellsO12 $$ Houtw3
  obtain ⟨word3, hw3Shape⟩ := List.length_eq_one_iff.mp hw3Cells
  isimp only [hw3Shape] at Houtw3array
  ihave Houtw3 :=
    ByteSlice_of_cells (out + 12) [word3] (hofcO12 word3) $$ Houtw3array
  ihave Houthigh :=
    ByteSlice_glue (out + 8) (WordCodec.u32le.serialize [word2])
      (WordCodec.u32le.serialize [word3]) 4 hw2Length $$ [Houtw2 Houtw3]
  · isplitl_exact Houtw2
    · irw_exact [hout12] with Houtw3
  ihave Hout :=
    ByteSlice_glue out (WordCodec.u32le.serialize [word0, word1])
      (WordCodec.u32le.serialize [word2] ++ WordCodec.u32le.serialize [word3])
      8 hrecLow8 $$ [Houtlow Houthigh]
  · isplitl_exact Houtlow
    · irw_exact [hout8] with Houthigh
  isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil, List.append_assoc] at Hout
  -- the record, unchanged
  isimp only [hrecZero] at Hrecword
  ihave Hreclow :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 record
      (WordCodec.u32le.serialize [word0, word1]) hrecLow8).mpr $$ [Hrecword]
  · isplitl_pureexact hwordR0
    iexact Hrecword
  ihave Hrechigharray : arrayAt 0 (record + 8) [word2] $$ [Hreccell]
  · isimp only [arrayAt]
    iframe Hreccell
  ihave Hrechigh :=
    ByteSlice_of_cells (record + 8) [word2] hofcR8 $$ Hrechigharray
  ihave Hrecord :=
    ByteSlice_glue record (WordCodec.u32le.serialize [word0, word1])
      (WordCodec.u32le.serialize [word2]) 8 hrecLow8 $$ [Hreclow Hrechigh]
  · isplitl_exact Hreclow
    · irw_exact [hrec8] with Hrechigh
  isimp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil, List.append_assoc] at Hrecord
  -- the red zone, as bytes again
  isimp only [hfZero] at Hb0word
  ihave Hb0 :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32)
      (WordCodec.u32le.serialize [word0, word1]) hrecLow8).mpr $$ [Hb0word]
  · isplitl_pureexact hwordF0
    iexact Hb0word
  ihave Hb1 :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32 + 8)
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
      hg3Length).mpr $$ [Hb1word]
  · isplitl_pureexact hwordF8
    iexact Hb1word
  ihave Hb2 :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32 + 16)
      (WordCodec.u32le.serialize [word0, word1]) hrecLow8).mpr $$ [Hb2word]
  · isplitl_pureexact hwordF16
    iexact Hb2word
  ihave Hb3 :=
    (Wasm.RustStd.HashMap.Table.ByteSlice_eight_as_u64 0 (sp - 32 + 24)
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
      hg3Length).mpr $$ [Hb3word]
  · isplitl_pureexact hwordF24
    iexact Hb3word
  ihave Hupper :=
    ByteSlice_glue (sp - 32 + 16) (WordCodec.u32le.serialize [word0, word1])
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
      8 hrecLow8 $$ [Hb2 Hb3]
  · isplitl_exact Hb2
    · irw_exact [hf24] with Hb3
  ihave Hmiddle :=
    ByteSlice_glue (sp - 32 + 8)
      (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
      (WordCodec.u32le.serialize [word0, word1]
        ++ (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad)))
      8 hg3Length $$ [Hb1 Hupper]
  · isplitl_exact Hb1
    · irw_exact [hf16] with Hupper
  ihave Hframe :=
    ByteSlice_glue (sp - 32) (WordCodec.u32le.serialize [word0, word1])
      ((WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
        ++ (WordCodec.u32le.serialize [word0, word1]
          ++ (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))))
      8 hrecLow8 $$ [Hb0 Hmiddle]
  · isplitl_exact Hb0
    · irw_exact [hf8] with Hmiddle
  ihave Hbelow :=
    StackBelow_intro sp (sp - 32) func53Depth
      (WordCodec.u32le.serialize [word0, word1]
        ++ ((WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
          ++ (WordCodec.u32le.serialize [word0, word1]
            ++ (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad)))))
      (by simp [hpadLength, hdepth53]) hbase32 $$ Hframe
  ihave Hsp : StackPointer sp $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iclose_map_runtime Hruntime with Hmodule Henv
  ihave Hnormal := Hcont $$ %word3
    %(WordCodec.u32le.serialize [word0, word1]
      ++ ((WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad))
        ++ (WordCodec.u32le.serialize [word0, word1]
          ++ (WordCodec.u32le.serialize [word2] ++ ([kind.toUInt8] ++ pad)))))
  ihave Hresume := Hnormal $$ Hruntime Hsp Hbelow Hout Hrecord
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hresume
  iexact Hresume

end Project.RustHashMap.Func53Proof
