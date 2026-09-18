import Project.RustHashMap.KeyDecoderContract
import Project.RustHashMap.Func1Proof
import Project.RustHashMap.Func49Proof
import Project.RustHashMap.DeallocNoop
import Project.RustHashMap.DriverTailProof

/-!
# Proof of the key-and-map decoder body

Local `func7`, absolute `func 10`, reads an input shaped `key ++ map`.
-/

namespace Wasm.SmallStep

section keyDecoderStore

open Iris Iris.ProgramLogic Language.Notation
open Wasm.SepLogic

variable {hlc : outParam HasLC} {α : Type}
variable [WasmSmallStepGS hlc α]
variable {Terminal : Type}
variable [view : TerminalView α Terminal]
local instance (priority := high) activeTerminalLanguageKeyStore :
    Language (Expr α) (MachineStore α) StepKind Terminal :=
  TerminalView.canonicalLanguage
local instance (priority := high) activeTerminalIrisGSKeyStore :
    @IrisGS_gen hlc (Expr α) Terminal (MachineStore α) StepKind
      activeTerminalLanguageKeyStore (WasmHeapGF α) :=
  { numLatersPerStep _ := 0
    forkPost _ := iprop(True)
    stateInterp_mono _ _ _ _ := by iintro $ }
variable {s : Stuckness} {E : CoPset}
variable {Φ : Terminal → IProp (WasmHeapGF α)}

/-- Total rule for `i64.store32` under every terminal view.  The
instruction writes the low four bytes of a 64-bit operand, so the resource
is a `pointsTo_u32` and the new value is the truncated operand.  The proof
follows `twp_store32` at `SmallStepTotalLifting.lean:899`, and the partial
rule `wp_store32I64` at `SmallStepLifting.lean:2459` names the same
step. -/
theorem twp_store32I64
    {params localValues values : List Value}
    {address offset : UInt32} {value : UInt64} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (oldWord : UInt32)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat)
    (h1 : ((address + offset) + 1).toNat =
      (address + offset).toNat + 1)
    (h2 : ((address + offset) + 2).toNat =
      (address + offset).toNat + 2)
    (h3 : ((address + offset) + 3).toNat =
      (address + offset).toNat + 3) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
        .store32I64 offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo_u32 0 (address + offset) oldWord -∗
    (pointsTo_u32 0 (address + offset) value.toUInt32 -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  wasm_twp_start_with iintro Hword Htwp
  ihave_pure Hfacts :
      ⌜store.wasm.mem.read32 (address + offset) = oldWord ∧
        (address + offset).toNat + 4 ≤
          store.wasm.mem.pages * 65536⌝ using
    stateInterp_pointsTo_u32_facts store ns obs nt
      (address + offset) oldWord h1 h2 h3 $$ [Hσ Hword]
  have hbound : address.toNat + offset.toNat + 4 ≤
      store.wasm.mem.pages * 65536 := by simpa only [hnowrap] using Hfacts.2
  have expectedStep : Step
      ⟨.running
        ⟨⟨params, localValues, .i64 value :: .i32 address :: values⟩,
          .store32I64 offset :: code, arity, remainder, controls, calls⟩,
        store⟩
      (.instruction (.store32I64 offset))
      ⟨.running
        ⟨⟨params, localValues, values⟩,
          code, arity, remainder, controls, calls⟩,
        { store with wasm :=
            { store.wasm with
              mem := store.wasm.mem.write32 (address + offset)
                value.toUInt32 } }⟩ :=
    Step.store32I64 (α := α) (address := Value.i32 address) rfl hbound
  wasm_twp_step expectedStep =>
    imod stateInterp_store32 store ns obs nt
        (address + offset) oldWord value.toUInt32 h1 h2 h3 Hfacts.2 $$
        [$Hσ $Hword] with ⟨Hσ, Hword⟩
    wasm_twp_frame
      iapply_exact Htwp with Hword

end keyDecoderStore

end Wasm.SmallStep

namespace Project.RustHashMap.Func7Proof

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open Project.RustHashMap.DecodeErrorContracts
open Project.RustHashMap.DeallocNoop
open Project.RustHashMap.KeyDecoderContract
open Project.RustHashMap.Decoder
open Project.RustHashMap.DriverTailProof
open scoped Wasm.SmallStep.Outcome

/-- The frame prologue.  It lowers the stack pointer by 96 and stores the
slice header. -/
def keyPrologue : Program :=
  [.globalGet 0, .const 96, .sub, .localTee 3, .globalSet 0,
    .localGet 3, .localGet 2, .store32 12,
    .localGet 3, .localGet 1, .store32 8]

/-- The innermost block.  It tests the input length and reads the key. -/
def guardBody : Program :=
  [.localGet 2, .const 4, .ltU, .br_if 0,
    .localGet 3, .localGet 2, .const 4294967292, .add, .store32 12,
    .localGet 3, .localGet 1, .const 4, .add, .store32 8,
    .localGet 1, .load32 0, .localSet 4, .br 1]

/-- The short-input arm builds the `io::Error` record. -/
def shortMake : Program :=
  [.localGet 3, .const 80, .add, .const 17, .const 1049080, .const 27,
    .call 55]

/-- The short-input arm moves the tail of the record out of the way, tests
word 0 of the record, and moves the tail back. -/
def shortShuffle : Program :=
  [.localGet 3, .localGet 3, .load64 84, .store64 64,
    .localGet 3, .localGet 3, .load32 92, .store32 72,
    .const 0, .localSet 4,
    .localGet 3, .load32 80, .localTee 2, .const 2147483649, .eq, .br_if 0,
    .localGet 3, .localGet 2, .store32 80,
    .localGet 3, .localGet 3, .load64 64, .store64 84,
    .localGet 3, .localGet 3, .load32 72, .store32 92]

/-- The short-input arm turns the record into the decode error. -/
def shortConvert : Program :=
  [.localGet 3, .const 48, .add, .localGet 3, .const 80, .add, .call 52,
    .localGet 3, .load32 48, .localTee 1, .const 2147483649, .eq, .br_if 0,
    .localGet 3, .load64 56, .localSet 5,
    .localGet 3, .load32 52, .localSet 2]

/-- The short-input arm without its branch. -/
def shortBuild : Program := shortMake ++ shortShuffle ++ shortConvert

/-- The short-input arm. -/
def shortArm : Program := shortBuild ++ [.br 1]

/-- The decoder call and the two tests that follow it. -/
def decodeCheck : Program :=
  [.localGet 3, .const 32, .add, .localGet 3, .const 8, .add, .call 4,
    .localGet 3, .load64 40, .localSet 5,
    .localGet 3, .load32 36, .localSet 2,
    .localGet 3, .load32 32, .localTee 1, .const 2147483649, .ne, .br_if 0,
    .localGet 5, .wrapI64, .localSet 1,
    .localGet 3, .load32 12, .eqz, .br_if 1]

/-- The trailing-bytes arm builds the decode error and copies it into the
output slot. -/
def trailingBuild : Program :=
  [.localGet 3, .const 16, .add, .const 12, .const 1049107, .const 18,
    .call 55,
    .localGet 0, .const 1, .store32 0,
    .localGet 0, .localGet 3, .load64 24, .store64 12,
    .localGet 0, .localGet 3, .load64 16, .store64 4]

/-- The trailing-bytes arm gives the buffer back. -/
def trailingFree : Program :=
  [.localGet 2, .eqz, .br_if 2,
    .localGet 1, .localGet 2, .const 3, .shl, .const 4, .call 60,
    .br 2]

/-- The decoder call and the arm that follows a trailing-bytes input. -/
def decodePart : Program :=
  decodeCheck ++ trailingBuild ++ trailingFree

/-- The stores of the rejecting exit. -/
def rejectStores : Program :=
  [.localGet 0, .localGet 5, .store64 12,
    .localGet 0, .localGet 2, .store32 8,
    .localGet 0, .localGet 1, .store32 4,
    .localGet 0, .const 1, .store32 0]

/-- The rejecting exit. -/
def rejectWrite : Program := rejectStores ++ [.br 1]

/-- The accepting exit. -/
def okWrite : Program :=
  [.localGet 0, .localGet 1, .store32 12,
    .localGet 0, .localGet 2, .store32 8,
    .localGet 0, .localGet 4, .store32 4,
    .localGet 0, .const 0, .store32 0,
    .localGet 0, .localGet 5, .constI64 32, .shrUI64, .store32I64 16]

/-- The stack epilogue. -/
def keyEpilogue : Program :=
  [.localGet 3, .const 96, .add, .globalSet 0]

/-- The body of the fourth block. -/
def body4 : Program := .block 0 0 guardBody :: shortArm

/-- The body of the third block. -/
def body3 : Program := .block 0 0 body4 :: decodePart

/-- The body of the second block. -/
def body2 : Program := .block 0 0 body3 :: rejectWrite

/-- The body of the first block. -/
def body1 : Program := .block 0 0 body2 :: okWrite

/-- The body is the prologue, one block, and the epilogue. -/
theorem func7_shape :
    Project.RustHashMap.func7 =
      keyPrologue ++ .block 0 0 body1 :: keyEpilogue := by
  rfl

/-! ## The pieces of the frame -/

/-- The 96 frame bytes, as the ten pieces that the body uses. -/
private theorem frame_pieces (bytes : List UInt8)
    (hlength : bytes.length = 96) :
    ∃ q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : List UInt8,
      bytes = q0 ++ (q1 ++ (q2 ++ (q3 ++ (q4 ++ (q5 ++ (q6 ++ (q7 ++
        (q8 ++ q9)))))))) ∧
      q0.length = 8 ∧ q1.length = 4 ∧ q2.length = 4 ∧ q3.length = 16 ∧
      q4.length = 16 ∧ q5.length = 16 ∧ q6.length = 8 ∧ q7.length = 4 ∧
      q8.length = 4 ∧ q9.length = 16 := by
  refine ⟨bytes.take 8, (bytes.drop 8).take 4,
    ((bytes.drop 8).drop 4).take 4,
    (((bytes.drop 8).drop 4).drop 4).take 16,
    ((((bytes.drop 8).drop 4).drop 4).drop 16).take 16,
    (((((bytes.drop 8).drop 4).drop 4).drop 16).drop 16).take 16,
    ((((((bytes.drop 8).drop 4).drop 4).drop 16).drop 16).drop 16).take 8,
    (((((((bytes.drop 8).drop 4).drop 4).drop 16).drop 16).drop 16).drop
      8).take 4,
    ((((((((bytes.drop 8).drop 4).drop 4).drop 16).drop 16).drop 16).drop
      8).drop 4).take 4,
    ((((((((bytes.drop 8).drop 4).drop 4).drop 16).drop 16).drop 16).drop
      8).drop 4).drop 4,
    by simp only [List.take_append_drop], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

/-- Cut a slice at a byte offset that a later address names. -/
private theorem cut_step [WasmHeapGS Universal.State]
    (base addr : UInt32) (lo hi : List UInt8) (k : Nat)
    (hlo : lo.length = k) (haddr : base + UInt32.ofNat k = addr) :
    Slices.ByteSlice 0 base (lo ++ hi) ⊢
      iprop(Slices.ByteSlice 0 base lo ∗ Slices.ByteSlice 0 addr hi) := by
  subst haddr
  iintro Hbytes
  ihave ⟨Hlow, Hhigh⟩ :=
    (Slices.ByteSlice_append 0 base lo hi).mp $$ Hbytes
  isplitl_exact Hlow
  · irw_exact [hlo] with Hhigh

/-- Glue a slice back at a byte offset that a later address names. -/
private theorem glue_step [WasmHeapGS Universal.State]
    (base addr : UInt32) (lo hi : List UInt8) (k : Nat)
    (hlo : lo.length = k) (haddr : base + UInt32.ofNat k = addr) :
    iprop(Slices.ByteSlice 0 base lo ∗ Slices.ByteSlice 0 addr hi) ⊢
      Slices.ByteSlice 0 base (lo ++ hi) := by
  subst haddr
  iintro ⟨Hlow, Hhigh⟩
  iapply (Slices.ByteSlice_append 0 base lo hi).mpr
  isplitl_exact Hlow
  · irw_exact [hlo] with Hhigh

/-- The ten addresses of the frame pieces. -/
private theorem frame_addresses (frame : UInt32) :
    frame + UInt32.ofNat 8 = frame + 8 ∧
      frame + (8 : UInt32) + UInt32.ofNat 4 = frame + 12 ∧
      frame + (12 : UInt32) + UInt32.ofNat 4 = frame + 16 ∧
      frame + (16 : UInt32) + UInt32.ofNat 16 = frame + 32 ∧
      frame + (32 : UInt32) + UInt32.ofNat 16 = frame + 48 ∧
      frame + (48 : UInt32) + UInt32.ofNat 16 = frame + 64 ∧
      frame + (64 : UInt32) + UInt32.ofNat 8 = frame + 72 ∧
      frame + (72 : UInt32) + UInt32.ofNat 4 = frame + 76 ∧
      frame + (76 : UInt32) + UInt32.ofNat 4 = frame + 80 :=
  ⟨rfl, frame_offset frame 8 4 12 rfl, frame_offset frame 12 4 16 rfl,
    frame_offset frame 16 16 32 rfl, frame_offset frame 32 16 48 rfl,
    frame_offset frame 48 16 64 rfl, frame_offset frame 64 8 72 rfl,
    frame_offset frame 72 4 76 rfl, frame_offset frame 76 4 80 rfl⟩

/-- The frame, cut into its ten pieces. -/
private theorem frame_cut [WasmHeapGS Universal.State]
    (frame : UInt32) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : List UInt8)
    (h0 : q0.length = 8) (h1 : q1.length = 4) (h2 : q2.length = 4)
    (h3 : q3.length = 16) (h4 : q4.length = 16) (h5 : q5.length = 16)
    (h6 : q6.length = 8) (h7 : q7.length = 4) (h8 : q8.length = 4) :
    Slices.ByteSlice 0 frame
        (q0 ++ (q1 ++ (q2 ++ (q3 ++ (q4 ++ (q5 ++ (q6 ++ (q7 ++
          (q8 ++ q9))))))))) ⊢
      iprop(Slices.ByteSlice 0 frame q0 ∗
        Slices.ByteSlice 0 (frame + 8) q1 ∗
        Slices.ByteSlice 0 (frame + 12) q2 ∗
        Slices.ByteSlice 0 (frame + 16) q3 ∗
        Slices.ByteSlice 0 (frame + 32) q4 ∗
        Slices.ByteSlice 0 (frame + 48) q5 ∗
        Slices.ByteSlice 0 (frame + 64) q6 ∗
        Slices.ByteSlice 0 (frame + 72) q7 ∗
        Slices.ByteSlice 0 (frame + 76) q8 ∗
        Slices.ByteSlice 0 (frame + 80) q9) := by
  obtain ⟨a8, a12, a16, a32, a48, a64, a72, a76, a80⟩ :=
    frame_addresses frame
  iintro Hbytes
  ihave ⟨H0, Hr1⟩ := cut_step frame (frame + 8) q0 _ 8 h0 a8 $$ Hbytes
  ihave ⟨H1, Hr2⟩ := cut_step (frame + 8) (frame + 12) q1 _ 4 h1 a12 $$ Hr1
  ihave ⟨H2, Hr3⟩ := cut_step (frame + 12) (frame + 16) q2 _ 4 h2 a16 $$ Hr2
  ihave ⟨H3, Hr4⟩ := cut_step (frame + 16) (frame + 32) q3 _ 16 h3 a32 $$ Hr3
  ihave ⟨H4, Hr5⟩ := cut_step (frame + 32) (frame + 48) q4 _ 16 h4 a48 $$ Hr4
  ihave ⟨H5, Hr6⟩ := cut_step (frame + 48) (frame + 64) q5 _ 16 h5 a64 $$ Hr5
  ihave ⟨H6, Hr7⟩ := cut_step (frame + 64) (frame + 72) q6 _ 8 h6 a72 $$ Hr6
  ihave ⟨H7, Hr8⟩ := cut_step (frame + 72) (frame + 76) q7 _ 4 h7 a76 $$ Hr7
  ihave ⟨H8, H9⟩ := cut_step (frame + 76) (frame + 80) q8 _ 4 h8 a80 $$ Hr8
  isplitl_exacts [H0 H1 H2 H3 H4 H5 H6 H7 H8]
  iexact H9

/-- The frame, whole again. -/
private theorem frame_glue [WasmHeapGS Universal.State]
    (frame : UInt32) (q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 : List UInt8)
    (h0 : q0.length = 8) (h1 : q1.length = 4) (h2 : q2.length = 4)
    (h3 : q3.length = 16) (h4 : q4.length = 16) (h5 : q5.length = 16)
    (h6 : q6.length = 8) (h7 : q7.length = 4) (h8 : q8.length = 4) :
    iprop(Slices.ByteSlice 0 frame q0 ∗
        Slices.ByteSlice 0 (frame + 8) q1 ∗
        Slices.ByteSlice 0 (frame + 12) q2 ∗
        Slices.ByteSlice 0 (frame + 16) q3 ∗
        Slices.ByteSlice 0 (frame + 32) q4 ∗
        Slices.ByteSlice 0 (frame + 48) q5 ∗
        Slices.ByteSlice 0 (frame + 64) q6 ∗
        Slices.ByteSlice 0 (frame + 72) q7 ∗
        Slices.ByteSlice 0 (frame + 76) q8 ∗
        Slices.ByteSlice 0 (frame + 80) q9) ⊢
      Slices.ByteSlice 0 frame
        (q0 ++ (q1 ++ (q2 ++ (q3 ++ (q4 ++ (q5 ++ (q6 ++ (q7 ++
          (q8 ++ q9))))))))) := by
  obtain ⟨a8, a12, a16, a32, a48, a64, a72, a76, a80⟩ :=
    frame_addresses frame
  iintro ⟨H0, H1, H2, H3, H4, H5, H6, H7, H8, H9⟩
  ihave Hr8 := glue_step (frame + 76) (frame + 80) q8 q9 4 h8 a80 $$ [H8 H9]
  · isplitl_exact H8
    · iexact H9
  ihave Hr7 := glue_step (frame + 72) (frame + 76) q7 _ 4 h7 a76 $$ [H7 Hr8]
  · isplitl_exact H7
    · iexact Hr8
  ihave Hr6 := glue_step (frame + 64) (frame + 72) q6 _ 8 h6 a72 $$ [H6 Hr7]
  · isplitl_exact H6
    · iexact Hr7
  ihave Hr5 := glue_step (frame + 48) (frame + 64) q5 _ 16 h5 a64 $$ [H5 Hr6]
  · isplitl_exact H5
    · iexact Hr6
  ihave Hr4 := glue_step (frame + 32) (frame + 48) q4 _ 16 h4 a48 $$ [H4 Hr5]
  · isplitl_exact H4
    · iexact Hr5
  ihave Hr3 := glue_step (frame + 16) (frame + 32) q3 _ 16 h3 a32 $$ [H3 Hr4]
  · isplitl_exact H3
    · iexact Hr4
  ihave Hr2 := glue_step (frame + 12) (frame + 16) q2 _ 4 h2 a16 $$ [H2 Hr3]
  · isplitl_exact H2
    · iexact Hr3
  ihave Hr1 := glue_step (frame + 8) (frame + 12) q1 _ 4 h1 a12 $$ [H1 Hr2]
  · isplitl_exact H1
    · iexact Hr2
  iapply glue_step frame (frame + 8) q0 _ 8 h0 a8
  isplitl_exact H0
  · iexact Hr1

/-! ## Words and byte blocks -/

/-- Four owned bytes hold one word. -/
private theorem word_bytes (bytes : List UInt8) (hlength : bytes.length = 4) :
    ∃ w : UInt32, bytes = WordCodec.u32le.serialize [w] := by
  obtain ⟨hser, hlen⟩ :=
    Slices.u32le_serialize_decodeWords_of_length bytes 1 (by omega)
  obtain ⟨w, hw⟩ := one_word (Slices.decodeWords bytes) hlen
  exact ⟨w, by rw [← hser, hw]⟩

/-- Sixteen owned bytes hold four words. -/
private theorem four_word_bytes (bytes : List UInt8)
    (hlength : bytes.length = 16) :
    ∃ a b c d : UInt32,
      bytes = WordCodec.u32le.serialize [a, b, c, d] := by
  obtain ⟨hser, hlen⟩ :=
    Slices.u32le_serialize_decodeWords_of_length bytes 4 (by omega)
  obtain ⟨a, b, c, d, hw⟩ := four_words (Slices.decodeWords bytes) hlen
  exact ⟨a, b, c, d, by rw [← hser, hw]⟩

/-- One owned word is four owned bytes. -/
private theorem ByteSlice_of_one_word [WasmHeapGS Universal.State]
    (ptr w : UInt32) (hbound : ptr.toNat + 4 < UInt32.size) :
    pointsTo_u32 0 ptr w ⊢
      Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w]) := by
  iintro Hword
  iapply ByteSlice_of_cells ptr [w] (by simpa using hbound)
  isimp only [arrayAt]
  isplitl_exacts [Hword]
  exact .rfl

/-- Four owned bytes are one owned word. -/
private theorem one_word_of_ByteSlice [WasmHeapGS Universal.State]
    (ptr w : UInt32) :
    Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w]) ⊢
      pointsTo_u32 0 ptr w := by
  iintro Hbytes
  ihave Harray := cells_of_ByteSlice ptr [w] $$ Hbytes
  isimp only [arrayAt] at Harray
  icases Harray with ⟨H0, _Hemp⟩
  iexact H0

/-- Four owned words are sixteen owned bytes. -/
private theorem ByteSlice_of_four_words [WasmHeapGS Universal.State]
    (ptr w0 w1 w2 w3 : UInt32)
    (hbound : ptr.toNat + 16 < UInt32.size) :
    iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3) ⊢
      Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) := by
  iintro ⟨H0, H1, H2, H3⟩
  iapply ByteSlice_of_cells ptr [w0, w1, w2, w3] (by simpa using hbound)
  isimp only [arrayAt]
  isplitl_exacts [H0 H1 H2 H3]
  exact .rfl

/-- Sixteen owned bytes that hold four words are four owned words. -/
private theorem four_words_of_ByteSlice [WasmHeapGS Universal.State]
    (ptr w0 w1 w2 w3 : UInt32) :
    Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) ⊢
      iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 4 + 4) w2 ∗
        pointsTo_u32 0 (ptr + 4 + 4 + 4) w3) := by
  iintro Hbytes
  ihave Harray := cells_of_ByteSlice ptr [w0, w1, w2, w3] $$ Hbytes
  isimp only [arrayAt] at Harray
  icases Harray with ⟨H0, H1, H2, H3, _Hemp⟩
  isplitl_exacts [H0 H1 H2]
  iexact H3

/-! ## The two halves of a packed pair of words -/

/-- `i32.wrap_i64` on a packed pair gives the low word. -/
private theorem wrap_low (lo hi : UInt32) :
    UInt32.ofNat ((lo.toUInt64 ||| (hi.toUInt64 <<< 32)).toNat % 2 ^ 32)
      = lo := by
  rw [UInt32.ofNat_mod_size, UInt32.ofNat_uInt64ToNat]
  apply UInt32.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_or,
    UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64]
  apply BitVec.eq_of_getLsbD_eq
  intro i hbit
  simp (disch := omega)

/-- A right shift of 32 on a packed pair gives the high word. -/
private theorem shift_high (lo hi : UInt32) :
    ((lo.toUInt64 ||| (hi.toUInt64 <<< 32)) >>> (32 % 64)).toUInt32
      = hi := by
  apply UInt32.toBitVec_inj.mp
  simp only [UInt64.toBitVec_toUInt32, UInt64.toBitVec_shiftRight,
    UInt64.toBitVec_or, UInt64.toBitVec_shiftLeft, UInt32.toBitVec_toUInt64]
  apply BitVec.eq_of_getLsbD_eq
  intro i hbit
  simp (disch := omega)

/-! ## The addresses of the frame -/

/-- Every frame offset that the body uses adds without a wrap. -/
private theorem frame_addr_facts (base : UInt32)
    (h : base.toNat + 96 < UInt32.size) :
    (base + 8).toNat = base.toNat + 8 ∧
      (base + 12).toNat = base.toNat + 12 ∧
      (base + 16).toNat = base.toNat + 16 ∧
      (base + 32).toNat = base.toNat + 32 ∧
      (base + 48).toNat = base.toNat + 48 ∧
      (base + 52).toNat = base.toNat + 52 ∧
      (base + 56).toNat = base.toNat + 56 ∧
      (base + 60).toNat = base.toNat + 60 ∧
      (base + 64).toNat = base.toNat + 64 ∧
      (base + 72).toNat = base.toNat + 72 ∧
      (base + 76).toNat = base.toNat + 76 ∧
      (base + 80).toNat = base.toNat + 80 ∧
      (base + 84).toNat = base.toNat + 84 ∧
      (base + 92).toNat = base.toNat + 92 := by
  refine ⟨Slices.byteOffset_toNat base 8 (by omega),
    Slices.byteOffset_toNat base 12 (by omega),
    Slices.byteOffset_toNat base 16 (by omega),
    Slices.byteOffset_toNat base 32 (by omega),
    Slices.byteOffset_toNat base 48 (by omega),
    Slices.byteOffset_toNat base 52 (by omega),
    Slices.byteOffset_toNat base 56 (by omega),
    Slices.byteOffset_toNat base 60 (by omega),
    Slices.byteOffset_toNat base 64 (by omega),
    Slices.byteOffset_toNat base 72 (by omega),
    Slices.byteOffset_toNat base 76 (by omega),
    Slices.byteOffset_toNat base 80 (by omega),
    Slices.byteOffset_toNat base 84 (by omega),
    Slices.byteOffset_toNat base 92 (by omega)⟩
set_option maxHeartbeats 2000000 in
/-- The first part of the short-input arm.  It lends the 27-byte message at
1049080 to absolute `func 55`, which builds an `io::Error` record at
`frame + 80`.  Word 0 of the record is not `okTag`. -/
private theorem twp_short_error [WasmSmallStepGS hlc Universal.State]
    (out ptr len frame : UInt32) (heapId : GName)
    (errA dataBytes lower : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (l4 l5 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (herrLength : errA.length = 16)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : decoderDepth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 96 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame decoderDepth lower ∗
      Slices.ByteSlice 0 (frame + 80) errA ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ w0 : UInt32, ∀ w1 : UInt32, ∀ w2 : UInt32, ∀ w3 : UInt32,
          ∀ lower' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame decoderDepth lower' -∗
          Slices.ByteSlice 0 (frame + 80)
            (WordCodec.u32le.serialize [w0, w1, w2, w3]) -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜w0 ≠ okTag⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 ptr, .i32 len],
                  [.i32 frame, l4, l5], stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 ptr, .i32 len], [.i32 frame, l4, l5], stack⟩,
            shortMake ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Herr, Hdata, Hbump, Hstreams, Hcont⟩
  have hokTag : okTag = (2147483649 : UInt32) := rfl
  have h27 : (27 : UInt32).toNat = 27 := rfl
  have hdeep : decoderDepth = 240 := rfl
  have herrN : errorNewDepth = 160 := rfl
  have hconvD : func49Depth = 176 := rfl
  have hdataLen : dataBytes.length = 920 := by rw [hdataLength]; rfl
  have hE160 : errorNewDepth ≤ frame.toNat := by omega
  have b84 : frame.toNat + 84 + 8 ≤ UInt32.size := by omega
  have b64 : frame.toNat + 64 + 8 ≤ UInt32.size := by omega
  have b56 : frame.toNat + 56 + 8 ≤ UInt32.size := by omega
  have b92 : frame.toNat + 92 + 4 ≤ UInt32.size := by omega
  have b72 : frame.toNat + 72 + 4 ≤ UInt32.size := by omega
  have b80 : frame.toNat + 80 + 4 ≤ UInt32.size := by omega
  have b48 : frame.toNat + 48 + 4 ≤ UInt32.size := by omega
  have b52 : frame.toNat + 52 + 4 ≤ UInt32.size := by omega
  obtain ⟨a8, a12, a16, a32, a48, a52, a56, a60, a64, a72, a76, a80, a84,
    a92⟩ := frame_addr_facts frame hframeNowrap
  have hout80 : (frame + 80).toNat + 16 < UInt32.size := by omega
  have hseg504 : entryStackTop + UInt32.ofNat 504 = 1049080 := by decide
  have hseg531 : (1049080 : UInt32) + UInt32.ofNat 27 = 1049107 := by decide
  obtain ⟨dpre, dmsg, dpost, hdataShape, hdpre, hdmsg, hdpost⟩ :=
    data_pieces dataBytes hdataLen
  -- the data segment lends its 27-byte message
  isimp only [hdataShape] at Hdata
  ihave ⟨Hdpre, Hdr1⟩ :=
    (Slices.ByteSlice_append 0 entryStackTop dpre (dmsg ++ dpost)).mp $$ Hdata
  isimp only [hdpre, hseg504] at Hdr1
  ihave ⟨Hdmsg, Hdpost⟩ :=
    (Slices.ByteSlice_append 0 1049080 dmsg dpost).mp $$ Hdr1
  isimp only [hdmsg, hseg531] at Hdpost
  -- the stack region that absolute `func 55` takes
  ihave ⟨Hbelow, %hbelowLength⟩ :=
    StackBelow_length frame decoderDepth lower $$ Hbelow
  have htake80 :
      (lower.take (decoderDepth - errorNewDepth)).length =
        decoderDepth - errorNewDepth := by
    rw [List.length_take, hbelowLength]
    omega
  ihave ⟨Hdeep1, Herrzone⟩ :=
    frame_split frame decoderDepth errorNewDepth lower (by decide) $$ Hbelow
  -- absolute `func 55` builds the `io::Error` at `frame + 80`
  simp only [shortMake, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (80 : UInt32) + frame = frame + 80 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_const twp_const twp_const]
  have Hnew : Func52Spec (hlc := hlc) :=
    Project.RustHashMap.Func52Proof.func52_correct
  unfold Func52Spec CallContract callExpr at Hnew
  simp only [List.cons_append, List.nil_append] at Hnew
  iapply Hnew (sp := frame) (out := frame + 80) (kind := 17)
    (msgPtr := 1049080) (msgLen := 27) (heapId := heapId) (outBefore := errA)
    (below := lower.drop (decoderDepth - errorNewDepth)) (msgBytes := dmsg)
    (storedCursor := storedCursor) (frontier := frontier) (history := history)
    (input := input) (output := output) (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 ptr, .i32 len],
        locals := [.i32 frame, l4, l5], values := [] })
    (stack := stack)
  isplitl_exacts [Hruntime Hsp Herrzone Herr Hdmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨herrLength, hE160, hout80, by decide, by decide,
      by rw [h27]; exact hdmsg⟩
  isplit
  · iintro %w0 %w1 %w2 %w3 %belowA %storedCursorA %frontierA %historyA
    iintro Hruntime Hsp Herrzone Herr Hdmsg Hbump Hstreams %hw0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    -- the data segment, whole again
    ihave Hdr1 :=
      ByteSlice_glue 1049080 dmsg dpost 27 hdmsg $$ [Hdmsg Hdpost]
    · isplitl_exact Hdmsg
      · irw_exact [hseg531] with Hdpost
    ihave Hdata :=
      ByteSlice_glue entryStackTop dpre (dmsg ++ dpost) 504 hdpre $$
        [Hdpre Hdr1]
    · isplitl_exact Hdpre
      · irw_exact [hseg504] with Hdr1
    isimp only [← hdataShape] at Hdata
    -- the stack region, whole again
    ihave Hbelow :=
      frame_join frame decoderDepth errorNewDepth
        (lower.take (decoderDepth - errorNewDepth)) belowA htake80
        (by decide) $$ [Hdeep1 Herrzone]
    · isplitl_exact Hdeep1
      · iexact Herrzone
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %w0 %w1 %w2 %w3
      %(lower.take (decoderDepth - errorNewDepth) ++ belowA)
      %storedCursorA %frontierA %historyA
    iapply Hnormal $$ Hruntime Hsp Hbelow Herr Hdata Hbump Hstreams %hw0
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

set_option maxHeartbeats 2000000 in
/-- The second part of the short-input arm.  It moves words 1 to 3 of the
record into the scratch cells, tests word 0 against `okTag`, and moves the
three words back.  The test fails, so the block does not end here. -/
private theorem twp_short_shuffle [WasmSmallStepGS hlc Universal.State]
    (out ptr len frame w0 w1 w2 w3 scratch4 : UInt32)
    (scratch8 : List UInt8)
    (l4 l5 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hscratchLength : scratch8.length = 8)
    (hw0 : w0 ≠ okTag)
    (hframeNowrap : frame.toNat + 96 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 (frame + 80)
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) ∗
      Slices.ByteSlice 0 (frame + 64) scratch8 ∗
      pointsTo_u32 0 (frame + 72) scratch4 ∗
      (Slices.ByteSlice 0 (frame + 80)
          (WordCodec.u32le.serialize [w0, w1, w2, w3]) -∗
        Slices.ByteSlice 0 (frame + 64)
          (WordCodec.u32le.serialize [w1, w2]) -∗
        pointsTo_u32 0 (frame + 72) w3 -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 ptr, .i32 w0],
                [.i32 frame, .i32 0, l5], stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 ptr, .i32 len], [.i32 frame, l4, l5], stack⟩,
            shortShuffle ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Herr, Hscr8, Hscr4, Hcont⟩
  have hokTag : okTag = (2147483649 : UInt32) := rfl
  have b84 : frame.toNat + 84 + 8 ≤ UInt32.size := by omega
  have b64 : frame.toNat + 64 + 8 ≤ UInt32.size := by omega
  have b56 : frame.toNat + 56 + 8 ≤ UInt32.size := by omega
  have b92 : frame.toNat + 92 + 4 ≤ UInt32.size := by omega
  have b72 : frame.toNat + 72 + 4 ≤ UInt32.size := by omega
  have b80 : frame.toNat + 80 + 4 ≤ UInt32.size := by omega
  have b48 : frame.toNat + 48 + 4 ≤ UInt32.size := by omega
  have b52 : frame.toNat + 52 + 4 ≤ UInt32.size := by omega
  obtain ⟨a8, a12, a16, a32, a48, a52, a56, a60, a64, a72, a76, a80, a84,
    a92⟩ := frame_addr_facts frame hframeNowrap
  have n80 : (frame + 80).toNat + 4 < UInt32.size := by omega
  have n92 : (frame + 92).toNat + 4 < UInt32.size := by omega
  have w84 : (frame + 84).toNat + 8 < UInt32.size := by omega
  have w64 : (frame + 64).toNat + 8 < UInt32.size := by omega
  have hfa84 := offset_facts64 frame 84 84 rfl b84
  have hfa64 := offset_facts64 frame 64 64 rfl b64
  have hfa56 := offset_facts64 frame 56 56 rfl b56
  obtain ⟨hf92, hf92a, hf92b, hf92c⟩ := offset_facts frame 92 92 rfl b92
  obtain ⟨hf72, hf72a, hf72b, hf72c⟩ := offset_facts frame 72 72 rfl b72
  obtain ⟨hf80, hf80a, hf80b, hf80c⟩ := offset_facts frame 80 80 rfl b80
  have e84 : frame + (80 : UInt32) + UInt32.ofNat 4 = frame + 84 :=
    frame_offset frame 80 4 84 rfl
  have e92 : frame + (84 : UInt32) + UInt32.ofNat 8 = frame + 92 :=
    frame_offset frame 84 8 92 rfl
  have hw0' : w0 ≠ (2147483649 : UInt32) := by rw [← hokTag]; exact hw0
  simp only [shortShuffle, List.cons_append, List.nil_append]
  -- the record splits into word 0, the middle pair and word 3
  isimp only [ser4_split121] at Herr
  ihave ⟨Herr0, Herr123⟩ :=
    (Slices.ByteSlice_append 0 (frame + 80) (WordCodec.u32le.serialize [w0])
      (WordCodec.u32le.serialize [w1, w2] ++
        WordCodec.u32le.serialize [w3])).mp $$ Herr
  isimp only [ser_one_length, e84] at Herr123
  ihave ⟨Herr12, Herr3⟩ :=
    (Slices.ByteSlice_append 0 (frame + 84)
      (WordCodec.u32le.serialize [w1, w2])
      (WordCodec.u32le.serialize [w3])).mp $$ Herr123
  isimp only [ser_two_length, e92] at Herr3
  -- the middle pair goes to the scratch block
  ihave Herr12w :=
    ByteSlice_as_word (frame + 84) (frame + 84)
      (WordCodec.u32le.serialize [w1, w2]) rfl (ser_two_length w1 w2) $$
      Herr12
  ihave Hscr8w :=
    ByteSlice_as_word (frame + 64) (frame + 64) scratch8 rfl
      hscratchLength $$ Hscr8
  wasm_twp_block_move
    (frame, 84, Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [w1, w2]), hfa84)
    (frame, 64, Wasm.RustStd.HashMap.Table.groupWord scratch8, hfa64)
    with Herr12w Hscr8w
  -- word 3 goes to the scratch word
  wasm_twp_pures [twp_localGet twp_localGet]
  ihave Herr3arr := cells_of_ByteSlice (frame + 92) [w3] $$ Herr3
  ihave ⟨Hw3, Hclose3⟩ :=
    cell_load (frame + 92) 0 [w3] 0 w3 (one_pos _) rfl (by decide) $$
      Herr3arr
  isimp only [UInt32.add_zero] at Hw3 Hclose3
  wasm_twp_rebind twp_load32 (address := frame) (offset := 92) w3
    hf92 hf92a hf92b hf92c with Hw3
  wasm_twp_rebind twp_store32 (address := frame) (offset := 72) scratch4
    hf72 hf72a hf72b hf72c with Hscr4
  -- the key of the step is zero
  wasm_twp_pures [twp_const]
  wasm_twp_localSet
  -- the dead `okTag` test of the `io::Error`
  wasm_twp_pures [twp_localGet]
  ihave Herr0arr := cells_of_ByteSlice (frame + 80) [w0] $$ Herr0
  ihave ⟨Hw0, Hclose0⟩ :=
    cell_load (frame + 80) 0 [w0] 0 w0 (one_pos _) rfl (by decide) $$
      Herr0arr
  isimp only [UInt32.add_zero] at Hw0 Hclose0
  wasm_twp_rebind twp_load32 (address := frame) (offset := 80) w0
    hf80 hf80a hf80b hf80c with Hw0
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  iapply twp_eq (result := 0) (by rw [if_neg hw0'])
  iapply twp_brIfZero
  -- word 0 goes back where it was
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := frame) (offset := 80) w0
    hf80 hf80a hf80b hf80c with Hw0
  ihave Herr0arr := Hclose0 $$ Hw0
  ihave Herr0 :=
    ByteSlice_of_cells (frame + 80) [w0]
      (cells_nowrap_one _ w0 n80) $$ Herr0arr
  -- the middle pair comes back
  wasm_twp_block_move
    (frame, 64, Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [w1, w2]), hfa64)
    (frame, 84, Wasm.RustStd.HashMap.Table.groupWord
      (WordCodec.u32le.serialize [w1, w2]), hfa84)
    with Hscr8w Herr12w
  -- word 3 comes back
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_load32 (address := frame) (offset := 72) w3
    hf72 hf72a hf72b hf72c with Hscr4
  wasm_twp_rebind twp_store32 (address := frame) (offset := 92) w3
    hf92 hf92a hf92b hf92c with Hw3
  ihave Herr3arr := Hclose3 $$ Hw3
  ihave Herr3 :=
    ByteSlice_of_cells (frame + 92) [w3]
      (cells_nowrap_one _ w3 n92) $$ Herr3arr
  -- the record, whole again
  ihave Herr12 :=
    ByteSlice_of_word (frame + 84) (frame + 84)
      (WordCodec.u32le.serialize [w1, w2]) rfl (ser_two_length w1 w2)
      w84 $$ Herr12w
  ihave Herr123 :=
    ByteSlice_glue (frame + 84) (WordCodec.u32le.serialize [w1, w2])
      (WordCodec.u32le.serialize [w3]) 8 (ser_two_length w1 w2) $$
      [Herr12 Herr3]
  · isplitl_exact Herr12
    · irw_exact [e92] with Herr3
  ihave Herr :=
    ByteSlice_glue (frame + 80) (WordCodec.u32le.serialize [w0])
      (WordCodec.u32le.serialize [w1, w2] ++
        WordCodec.u32le.serialize [w3]) 4 (ser_one_length w0) $$
      [Herr0 Herr123]
  · isplitl_exact Herr0
    · irw_exact [e84] with Herr123
  isimp only [← ser4_split121] at Herr
  -- the scratch block, as bytes again
  ihave Hscr8 :=
    ByteSlice_of_word (frame + 64) (frame + 64)
      (WordCodec.u32le.serialize [w1, w2]) rfl (ser_two_length w1 w2)
      w64 $$ Hscr8w
  iapply Hcont $$ Herr Hscr8 Hscr4

set_option maxHeartbeats 2000000 in
/-- The third part of the short-input arm.  It gives the record to absolute
`func 52`, which turns it into the decode error at `frame + 48`.  Word 0 of
the decode error is not `okTag`, so the block does not end here either.  The
body then reads the last three words of the decode error. -/
private theorem twp_short_convert [WasmSmallStepGS hlc Universal.State]
    (out ptr frame w0 w1 w2 w3 : UInt32) (heapId : GName)
    (convBefore dataBytes lower : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (l5 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hconvLength : convBefore.length = 16)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hw0 : w0 ≠ okTag)
    (hframeLow : decoderDepth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 96 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame decoderDepth lower ∗
      Slices.ByteSlice 0 (frame + 48) convBefore ∗
      Slices.ByteSlice 0 (frame + 80)
        (WordCodec.u32le.serialize [w0, w1, w2, w3]) ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ v0 : UInt32, ∀ v1 : UInt32, ∀ v2 : UInt32, ∀ v3 : UInt32,
          ∀ errAfter : List UInt8, ∀ lower' : List UInt8,
          ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
          ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame decoderDepth lower' -∗
          Slices.ByteSlice 0 (frame + 48)
            (WordCodec.u32le.serialize [v0, v1, v2, v3]) -∗
          Slices.ByteSlice 0 (frame + 80) errAfter -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜v0 ≠ okTag ∧ errAfter.length = 16⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 v0, .i32 v1],
                  [.i32 frame, .i32 0,
                    .i64 (v2.toUInt64 ||| (v3.toUInt64 <<< 32))], stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 ptr, .i32 w0],
              [.i32 frame, .i32 0, l5], stack⟩,
            shortConvert ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hconv, Herr, Hdata, Hbump, Hstreams,
    Hcont⟩
  have hokTag : okTag = (2147483649 : UInt32) := rfl
  have hdeep : decoderDepth = 240 := rfl
  have hconvD : func49Depth = 176 := rfl
  have hE176 : func49Depth ≤ frame.toNat := by omega
  have b84 : frame.toNat + 84 + 8 ≤ UInt32.size := by omega
  have b64 : frame.toNat + 64 + 8 ≤ UInt32.size := by omega
  have b56 : frame.toNat + 56 + 8 ≤ UInt32.size := by omega
  have b92 : frame.toNat + 92 + 4 ≤ UInt32.size := by omega
  have b72 : frame.toNat + 72 + 4 ≤ UInt32.size := by omega
  have b80 : frame.toNat + 80 + 4 ≤ UInt32.size := by omega
  have b48 : frame.toNat + 48 + 4 ≤ UInt32.size := by omega
  have b52 : frame.toNat + 52 + 4 ≤ UInt32.size := by omega
  obtain ⟨a8, a12, a16, a32, a48, a52, a56, a60, a64, a72, a76, a80, a84,
    a92⟩ := frame_addr_facts frame hframeNowrap
  have hout48 : (frame + 48).toNat + 16 < UInt32.size := by omega
  have herr80 : (frame + 80).toNat + 16 < UInt32.size := by omega
  have hfa56 := offset_facts64 frame 56 56 rfl b56
  obtain ⟨hf48, hf48a, hf48b, hf48c⟩ := offset_facts frame 48 48 rfl b48
  obtain ⟨hf52, hf52a, hf52b, hf52c⟩ := offset_facts frame 52 52 rfl b52
  have c52 : frame + (48 : UInt32) + 4 = frame + 52 := by
    rw [UInt32.add_assoc, show (48 : UInt32) + 4 = 52 from by decide]
  have c56 : frame + (52 : UInt32) + 4 = frame + 56 := by
    rw [UInt32.add_assoc, show (52 : UInt32) + 4 = 56 from by decide]
  have c60 : frame + (56 : UInt32) + 4 = frame + 60 := by
    rw [UInt32.add_assoc, show (56 : UInt32) + 4 = 60 from by decide]
  simp only [shortConvert, List.cons_append, List.nil_append]
  -- the stack region that absolute `func 52` takes
  ihave ⟨Hbelow, %hbelowLengthA⟩ :=
    StackBelow_length frame decoderDepth lower $$ Hbelow
  have htake64 :
      (lower.take (decoderDepth - func49Depth)).length =
        decoderDepth - func49Depth := by
    rw [List.length_take, hbelowLengthA]
    omega
  ihave ⟨Hdeep2, Hconvzone⟩ :=
    frame_split frame decoderDepth func49Depth lower (by decide) $$ Hbelow
  -- absolute `func 52` turns the record into the decode error
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (48 : UInt32) + frame = frame + 48 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (80 : UInt32) + frame = frame + 80 from UInt32.add_comm _ _]
  have Hturn : Func49Spec (hlc := hlc) :=
    Project.RustHashMap.Func49Proof.func49_correct
  unfold Func49Spec CallContract callExpr at Hturn
  simp only [List.cons_append, List.nil_append] at Hturn
  iapply Hturn (sp := frame) (out := frame + 48) (errPtr := frame + 80)
    (errWord0 := w0) (errWord1 := w1) (errWord2 := w2) (errWord3 := w3)
    (heapId := heapId) (outBefore := convBefore)
    (below := lower.drop (decoderDepth - func49Depth))
    (dataBytes := dataBytes) (storedCursor := storedCursor)
    (frontier := frontier) (history := history) (input := input)
    (output := output) (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 ptr, .i32 w0],
        locals := [.i32 frame, .i32 0, l5], values := [] })
    (stack := stack)
  isplitl_exacts [Hruntime Hsp Hconvzone Hconv Herr Hdata Hbump Hstreams]
  isplitl_pureexact
    ⟨hconvLength, hE176, hout48, herr80, hw0, hdataLength⟩
  isplit
  · iintro %v0 %v1 %v2 %v3 %errAfter %belowB %storedCursorB %frontierB
      %historyB
    iintro Hruntime Hsp Hconvzone Hslot Herr Hdata Hbump Hstreams %hvFacts
    obtain ⟨hv0, hafterLength⟩ := hvFacts
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    have hv0' : v0 ≠ (2147483649 : UInt32) := by rw [← hokTag]; exact hv0
    ihave ⟨Hv0, Hv1, Hv2, Hv3⟩ :=
      ByteSlice_four_words (frame + 48) v0 v1 v2 v3 $$ Hslot
    isimp only [c52] at Hv1
    isimp only [c52, c56] at Hv2
    isimp only [c52, c56, c60] at Hv3
    -- the live test of the decode error
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := frame) (offset := 48) v0
      hf48 hf48a hf48b hf48c with Hv0
    wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_const]
    iapply twp_eq (result := 0) (by rw [if_neg hv0'])
    iapply twp_brIfZero
    -- the last two words go to the pair local
    wasm_twp_pures [twp_localGet]
    ihave Hpair :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (frame + 56) v2 v3).mp $$ [Hv2 Hv3]
    · isplitl_exact Hv2
      · irw_exact [← c60] with Hv3
    wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := frame)
      (offset := 56) (v2.toUInt64 ||| (v3.toUInt64 <<< 32))
      hfa56.1 hfa56.2.1 hfa56.2.2.1 hfa56.2.2.2.1 hfa56.2.2.2.2.1
      hfa56.2.2.2.2.2.1 hfa56.2.2.2.2.2.2.1 hfa56.2.2.2.2.2.2.2 with Hpair
    wasm_twp_localSet
    -- word 1 goes to the capacity local
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32 (address := frame) (offset := 52) v1
      hf52 hf52a hf52b hf52c with Hv1
    wasm_twp_localSet
    -- the decode error, whole again
    ihave ⟨Hv2, Hv3⟩ :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (frame + 56) v2 v3).mpr $$ Hpair
    isimp only [← c52] at Hv1
    isimp only [← c52, ← c56] at Hv2
    isimp only [← c52, ← c56, ← c60] at Hv3
    ihave Hslot :=
      ByteSlice_of_four_words (frame + 48) v0 v1 v2 v3 hout48 $$
        [Hv0 Hv1 Hv2 Hv3]
    · isplitl_exacts [Hv0 Hv1 Hv2]
      iexact Hv3
    -- the stack region, whole again
    ihave Hbelow :=
      frame_join frame decoderDepth func49Depth
        (lower.take (decoderDepth - func49Depth)) belowB htake64
        (by decide) $$ [Hdeep2 Hconvzone]
    · isplitl_exact Hdeep2
      · iexact Hconvzone
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %v0 %v1 %v2 %v3 %errAfter
      %(lower.take (decoderDepth - func49Depth) ++ belowB)
      %storedCursorB %frontierB %historyB
    iapply Hnormal $$ Hruntime Hsp Hbelow Hslot Herr Hdata Hbump Hstreams
      %⟨hv0, hafterLength⟩
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

set_option maxHeartbeats 2000000 in
/-- The short-input arm, without the branch that leaves the block.
The arm is the three parts above, one after the other. -/
private theorem twp_short_build [WasmSmallStepGS hlc Universal.State]
    (out ptr len frame : UInt32) (heapId : GName)
    (convBefore scratch8 errA dataBytes lower : List UInt8)
    (scratch4 : UInt32)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (l4 l5 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hconvLength : convBefore.length = 16)
    (hscratchLength : scratch8.length = 8)
    (herrLength : errA.length = 16)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (hframeLow : decoderDepth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 96 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame decoderDepth lower ∗
      Slices.ByteSlice 0 (frame + 48) convBefore ∗
      Slices.ByteSlice 0 (frame + 64) scratch8 ∗
      pointsTo_u32 0 (frame + 72) scratch4 ∗
      Slices.ByteSlice 0 (frame + 80) errA ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ v0 : UInt32, ∀ v1 : UInt32, ∀ v2 : UInt32, ∀ v3 : UInt32,
          ∀ w1 : UInt32, ∀ w2 : UInt32, ∀ w3 : UInt32,
          ∀ errAfter : List UInt8, ∀ lower' : List UInt8,
          ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
          ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame decoderDepth lower' -∗
          Slices.ByteSlice 0 (frame + 48)
            (WordCodec.u32le.serialize [v0, v1, v2, v3]) -∗
          Slices.ByteSlice 0 (frame + 64)
            (WordCodec.u32le.serialize [w1, w2]) -∗
          pointsTo_u32 0 (frame + 72) w3 -∗
          Slices.ByteSlice 0 (frame + 80) errAfter -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜v0 ≠ okTag ∧ errAfter.length = 16⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 v0, .i32 v1],
                  [.i32 frame, .i32 0,
                    .i64 (v2.toUInt64 ||| (v3.toUInt64 <<< 32))], stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 ptr, .i32 len],
              [.i32 frame, l4, l5], stack⟩,
            shortBuild ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hconv, Hscr8, Hscr4, Herr, Hdata, Hbump,
    Hstreams, Hcont⟩
  simp only [shortBuild, List.append_assoc]
  iapply twp_short_error out ptr len frame heapId errA dataBytes lower
    storedCursor frontier history input output raised l4 l5 herrLength
    hdataLength hframeLow hframeNowrap
  isplitl_exacts [Hruntime Hsp Hbelow Herr Hdata Hbump Hstreams]
  isplit
  · iintro %w0 %w1 %w2 %w3 %lower1 %cursor1 %frontier1 %history1
    iintro Hruntime Hsp Hbelow Herr Hdata Hbump Hstreams %hw0
    iapply twp_short_shuffle out ptr len frame w0 w1 w2 w3 scratch4 scratch8
      l4 l5 hscratchLength hw0 hframeNowrap
    isplitl_exacts [Herr Hscr8 Hscr4]
    iintro Herr Hscr8 Hscr4
    iapply twp_short_convert out ptr frame w0 w1 w2 w3 heapId convBefore
      dataBytes lower1 cursor1 frontier1 history1 input output raised l5
      hconvLength hdataLength hw0 hframeLow hframeNowrap
    isplitl_exacts [Hruntime Hsp Hbelow Hconv Herr Hdata Hbump Hstreams]
    isplit
    · iintro %v0 %v1 %v2 %v3 %errAfter %lower2 %cursor2 %frontier2 %history2
      iintro Hruntime Hsp Hbelow Hslot Herr Hdata Hbump Hstreams %hvFacts
      ihave Hnormal := BI.and_elim_l $$ Hcont
      ihave Hnormal := Hnormal $$ %v0 %v1 %v2 %v3 %w1 %w2 %w3 %errAfter
        %lower2 %cursor2 %frontier2 %history2
      iapply Hnormal $$ Hruntime Hsp Hbelow Hslot Hscr8 Hscr4 Herr Hdata
        Hbump Hstreams %hvFacts
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

/-! ## The twenty-byte output slot -/

/-- A list of five words is five words. -/
private theorem five_words (values : List UInt32)
    (hlength : values.length = 5) :
    ∃ a b c d e : UInt32, values = [a, b, c, d, e] := by
  match values, hlength with
  | [a, b, c, d, e], _ => exact ⟨a, b, c, d, e, rfl⟩

/-- Twenty owned bytes hold five words. -/
private theorem five_word_bytes (bytes : List UInt8)
    (hlength : bytes.length = 20) :
    ∃ a b c d e : UInt32,
      bytes = WordCodec.u32le.serialize [a, b, c, d, e] := by
  obtain ⟨hser, hlen⟩ :=
    Slices.u32le_serialize_decodeWords_of_length bytes 5 (by omega)
  obtain ⟨a, b, c, d, e, hw⟩ := five_words (Slices.decodeWords bytes) hlen
  exact ⟨a, b, c, d, e, by rw [← hser, hw]⟩

/-- The three address steps of the output slot.  Each step goes from one
cell to the next. -/
private theorem out_addr_steps (out : UInt32) :
    out + (4 : UInt32) + 4 = out + 8 ∧
      out + (8 : UInt32) + 4 = out + 12 ∧
      out + (12 : UInt32) + 4 = out + 16 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [UInt32.add_assoc, show (4 : UInt32) + 4 = 8 from by decide]
  · rw [UInt32.add_assoc, show (8 : UInt32) + 4 = 12 from by decide]
  · rw [UInt32.add_assoc, show (12 : UInt32) + 4 = 16 from by decide]

/-- Five owned words are twenty owned bytes. -/
private theorem ByteSlice_of_five_words [WasmHeapGS Universal.State]
    (ptr w0 w1 w2 w3 w4 : UInt32)
    (hbound : ptr.toNat + 20 < UInt32.size) :
    iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 8) w2 ∗ pointsTo_u32 0 (ptr + 12) w3 ∗
        pointsTo_u32 0 (ptr + 16) w4) ⊢
      Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3, w4]) := by
  iintro ⟨H0, H1, H2, H3, H4⟩
  obtain ⟨s8, s12, s16⟩ := out_addr_steps ptr
  iapply ByteSlice_of_cells ptr [w0, w1, w2, w3, w4] (by simpa using hbound)
  isimp only [arrayAt]
  isimp only [s8, s12, s16]
  isplitl_exacts [H0 H1 H2 H3 H4]
  exact .rfl

/-- Twenty owned bytes that hold five words are five owned words. -/
private theorem five_words_of_ByteSlice [WasmHeapGS Universal.State]
    (ptr w0 w1 w2 w3 w4 : UInt32) :
    Slices.ByteSlice (α := Universal.State) 0 ptr
        (WordCodec.u32le.serialize [w0, w1, w2, w3, w4]) ⊢
      iprop(pointsTo_u32 0 ptr w0 ∗ pointsTo_u32 0 (ptr + 4) w1 ∗
        pointsTo_u32 0 (ptr + 8) w2 ∗ pointsTo_u32 0 (ptr + 12) w3 ∗
        pointsTo_u32 0 (ptr + 16) w4) := by
  iintro Hbytes
  obtain ⟨s8, s12, s16⟩ := out_addr_steps ptr
  ihave Harray := cells_of_ByteSlice ptr [w0, w1, w2, w3, w4] $$ Hbytes
  isimp only [arrayAt] at Harray
  isimp only [s8, s12, s16] at Harray
  icases Harray with ⟨H0, H1, H2, H3, H4, _Hemp⟩
  isplitl_exacts [H0 H1 H2 H3]
  iexact H4

/-! ## The two exits that fill the output slot -/

set_option maxHeartbeats 2000000 in
/-- The stores of the rejecting exit.  They put the tag 1 and the four
words of the decode error into the output slot. -/
private theorem twp_reject_stores [WasmSmallStepGS hlc Universal.State]
    (out a b c d frame : UInt32) (outBefore : List UInt8) (l4 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hlength : outBefore.length = 20)
    (hbound : out.toNat + 20 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      (Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [1, a, b, c, d]) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 a, .i32 b],
                [.i32 frame, l4,
                  .i64 (c.toUInt64 ||| (d.toUInt64 <<< 32))], stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 a, .i32 b],
              [.i32 frame, l4,
                .i64 (c.toUInt64 ||| (d.toUInt64 <<< 32))], stack⟩,
            rejectStores ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hcont⟩
  have hzero : out + 0 = out := UInt32.add_zero out
  have b12 : out.toNat + 12 + 8 ≤ UInt32.size := by omega
  have b8 : out.toNat + 8 + 4 ≤ UInt32.size := by omega
  have b4 : out.toNat + 4 + 4 ≤ UInt32.size := by omega
  have b0 : out.toNat + 0 + 4 ≤ UInt32.size := by omega
  have hfa12 := offset_facts64 out 12 12 rfl b12
  obtain ⟨hf8, hf8a, hf8b, hf8c⟩ := offset_facts out 8 8 rfl b8
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts out 4 4 rfl b4
  obtain ⟨hf0, hf0a, hf0b, hf0c⟩ := offset_facts out 0 0 rfl b0
  obtain ⟨_s8, _s12, s16'⟩ := out_addr_steps out
  obtain ⟨o0, o1, o2, o3, o4, hout⟩ := five_word_bytes outBefore hlength
  isimp only [hout] at Hout
  ihave ⟨H0, H1, H2, H3, H4⟩ :=
    five_words_of_ByteSlice out o0 o1 o2 o3 o4 $$ Hout
  simp only [rejectStores, List.cons_append, List.nil_append]
  ihave Hpair :=
    (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
      (out + 12) o3 o4).mp $$ [H3 H4]
  · isplitl_exact H3
    · irw_exact [s16'] with H4
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store64 (address := out) (offset := 12)
    (o3.toUInt64 ||| (o4.toUInt64 <<< 32))
    hfa12.1 hfa12.2.1 hfa12.2.2.1 hfa12.2.2.2.1 hfa12.2.2.2.2.1
    hfa12.2.2.2.2.2.1 hfa12.2.2.2.2.2.2.1 hfa12.2.2.2.2.2.2.2 with Hpair
  ihave ⟨H3, H4⟩ :=
    (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
      (out + 12) c d).mpr $$ Hpair
  isimp only [s16'] at H4
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 8) o2
    hf8 hf8a hf8b hf8c with H2
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 4) o1
    hf4 hf4a hf4b hf4c with H1
  wasm_twp_pures [twp_localGet twp_const]
  ihave H0 := word_move out (out + 0) o0 hzero $$ H0
  wasm_twp_rebind twp_store32 (address := out) (offset := 0) o0
    hf0 hf0a hf0b hf0c with H0
  ihave H0 := word_move (out + 0) out 1 hzero.symm $$ H0
  iapply Hcont
  iapply ByteSlice_of_five_words out 1 a b c d hbound
  isplitl_exacts [H0 H1 H2 H3]
  iexact H4

set_option maxHeartbeats 2000000 in
/-- The stores of the accepting exit.  They put the tag 0, the key, the
capacity, the buffer and the pair count into the output slot. -/
private theorem twp_ok_write [WasmSmallStepGS hlc Universal.State]
    (out buffer capacity key count frame : UInt32) (outBefore : List UInt8)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hlength : outBefore.length = 20)
    (hbound : out.toNat + 20 < UInt32.size) :
    iprop(
      Slices.ByteSlice 0 out outBefore ∗
      (Slices.ByteSlice 0 out
          (WordCodec.u32le.serialize [0, key, capacity, buffer, count]) -∗
        WP (.running
            ⟨⟨[.i32 out, .i32 buffer, .i32 capacity],
                [.i32 frame, .i32 key,
                  .i64 (buffer.toUInt64 ||| (count.toUInt64 <<< 32))],
              stack⟩,
              code, arity, remainder, controls, calls⟩
            : Expr Universal.State) @ s; E [{ Φ }])) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 buffer, .i32 capacity],
              [.i32 frame, .i32 key,
                .i64 (buffer.toUInt64 ||| (count.toUInt64 <<< 32))],
            stack⟩,
            okWrite ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hout, Hcont⟩
  have hzero : out + 0 = out := UInt32.add_zero out
  have b16 : out.toNat + 16 + 4 ≤ UInt32.size := by omega
  have b12 : out.toNat + 12 + 4 ≤ UInt32.size := by omega
  have b8 : out.toNat + 8 + 4 ≤ UInt32.size := by omega
  have b4 : out.toNat + 4 + 4 ≤ UInt32.size := by omega
  have b0 : out.toNat + 0 + 4 ≤ UInt32.size := by omega
  obtain ⟨hf16, hf16a, hf16b, hf16c⟩ := offset_facts out 16 16 rfl b16
  obtain ⟨hf12, hf12a, hf12b, hf12c⟩ := offset_facts out 12 12 rfl b12
  obtain ⟨hf8, hf8a, hf8b, hf8c⟩ := offset_facts out 8 8 rfl b8
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts out 4 4 rfl b4
  obtain ⟨hf0, hf0a, hf0b, hf0c⟩ := offset_facts out 0 0 rfl b0
  obtain ⟨o0, o1, o2, o3, o4, hout⟩ := five_word_bytes outBefore hlength
  isimp only [hout] at Hout
  ihave ⟨H0, H1, H2, H3, H4⟩ :=
    five_words_of_ByteSlice out o0 o1 o2 o3 o4 $$ Hout
  simp only [okWrite, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 12) o3
    hf12 hf12a hf12b hf12c with H3
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 8) o2
    hf8 hf8a hf8b hf8c with H2
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := out) (offset := 4) o1
    hf4 hf4a hf4b hf4c with H1
  wasm_twp_pures [twp_localGet twp_const]
  ihave H0 := word_move out (out + 0) o0 hzero $$ H0
  wasm_twp_rebind twp_store32 (address := out) (offset := 0) o0
    hf0 hf0a hf0b hf0c with H0
  ihave H0 := word_move (out + 0) out 0 hzero.symm $$ H0
  wasm_twp_pures [twp_localGet twp_localGet twp_constI64 twp_shrUI64]
  wasm_twp_rebind twp_store32I64 (address := out) (offset := 16) o4
    hf16 hf16a hf16b hf16c with H4
  isimp only [shift_high] at H4
  iapply Hcont
  iapply ByteSlice_of_five_words out 0 key capacity buffer count hbound
  isplitl_exacts [H0 H1 H2 H3]
  iexact H4

/-! ## The trailing-bytes arm -/

/-- The data segment, as the 18-byte message at 1049107 and the bytes on
each side of it. -/
private theorem data_pieces18 (bytes : List UInt8)
    (hlength : bytes.length = 920) :
    ∃ pre msg post : List UInt8,
      bytes = pre ++ (msg ++ post) ∧ pre.length = 531 ∧
        msg.length = 18 ∧ post.length = 371 := by
  refine ⟨bytes.take 531, (bytes.drop 531).take 18,
    (bytes.drop 531).drop 18, by simp only [List.take_append_drop], ?_, ?_,
    ?_⟩ <;>
    simp only [List.length_take, List.length_drop, hlength] <;> omega

set_option maxHeartbeats 2000000 in
/-- The trailing-bytes arm.  It lends the 18-byte message at 1049107 to
absolute `func 55`, which builds an `io::Error` record at `frame + 16`.
The arm then puts the tag 1 and the four words of the record into the
output slot. -/
private theorem twp_trailing_error [WasmSmallStepGS hlc Universal.State]
    (out frame : UInt32) (v1 v2 : Value) (heapId : GName)
    (errB outBefore dataBytes lower : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool) (l4 l5 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (herrLength : errB.length = 16)
    (houtLength : outBefore.length = 20)
    (hdataLength : dataBytes.length = dataSegmentSize)
    (houtNowrap : out.toNat + 20 < UInt32.size)
    (hframeLow : decoderDepth ≤ frame.toNat)
    (hframeNowrap : frame.toNat + 96 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame decoderDepth lower ∗
      Slices.ByteSlice 0 (frame + 16) errB ∗
      Slices.ByteSlice 0 out outBefore ∗
      Slices.ByteSlice 0 entryStackTop dataBytes ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ w0 : UInt32, ∀ w1 : UInt32, ∀ w2 : UInt32, ∀ w3 : UInt32,
          ∀ lower' : List UInt8, ∀ storedCursor' : UInt32,
          ∀ frontier' : Nat, ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame decoderDepth lower' -∗
          Slices.ByteSlice 0 (frame + 16)
            (WordCodec.u32le.serialize [w0, w1, w2, w3]) -∗
          Slices.ByteSlice 0 out
            (WordCodec.u32le.serialize [1, w0, w1, w2, w3]) -∗
          Slices.ByteSlice 0 entryStackTop dataBytes -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          ⌜w0 ≠ okTag⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, v1, v2], [.i32 frame, l4, l5], stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, v1, v2], [.i32 frame, l4, l5], stack⟩,
            trailingBuild ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Herr, Hout, Hdata, Hbump, Hstreams, Hcont⟩
  have h18 : (18 : UInt32).toNat = 18 := rfl
  have hdeep : decoderDepth = 240 := rfl
  have herrN : errorNewDepth = 160 := rfl
  have hdataLen : dataBytes.length = 920 := by rw [hdataLength]; rfl
  have hE160 : errorNewDepth ≤ frame.toNat := by omega
  obtain ⟨a8, a12, a16, a32, a48, a52, a56, a60, a64, a72, a76, a80, a84,
    a92⟩ := frame_addr_facts frame hframeNowrap
  have hout16 : (frame + 16).toNat + 16 < UInt32.size := by omega
  have b16 : frame.toNat + 16 + 8 ≤ UInt32.size := by omega
  have b24 : frame.toNat + 24 + 8 ≤ UInt32.size := by omega
  have c4 : out.toNat + 4 + 8 ≤ UInt32.size := by omega
  have c12 : out.toNat + 12 + 8 ≤ UInt32.size := by omega
  have c0 : out.toNat + 0 + 4 ≤ UInt32.size := by omega
  have hfa16 := offset_facts64 frame 16 16 rfl b16
  have hfa24 := offset_facts64 frame 24 24 rfl b24
  have hfaO4 := offset_facts64 out 4 4 rfl c4
  have hfaO12 := offset_facts64 out 12 12 rfl c12
  obtain ⟨hf0, hf0a, hf0b, hf0c⟩ := offset_facts out 0 0 rfl c0
  obtain ⟨s8, s12, s16⟩ := out_addr_steps out
  have hzero : out + 0 = out := UInt32.add_zero out
  have g20 : frame + (16 : UInt32) + 4 = frame + 20 := by
    rw [UInt32.add_assoc, show (16 : UInt32) + 4 = 20 from by decide]
  have g24 : frame + (20 : UInt32) + 4 = frame + 24 := by
    rw [UInt32.add_assoc, show (20 : UInt32) + 4 = 24 from by decide]
  have g28 : frame + (24 : UInt32) + 4 = frame + 28 := by
    rw [UInt32.add_assoc, show (24 : UInt32) + 4 = 28 from by decide]
  have hseg531 : entryStackTop + UInt32.ofNat 531 = 1049107 := by decide
  have hseg549 : (1049107 : UInt32) + UInt32.ofNat 18 = 1049125 := by decide
  obtain ⟨dpre, dmsg, dpost, hdataShape, hdpre, hdmsg, hdpost⟩ :=
    data_pieces18 dataBytes hdataLen
  -- the data segment lends its 18-byte message
  isimp only [hdataShape] at Hdata
  ihave ⟨Hdpre, Hdr1⟩ :=
    (Slices.ByteSlice_append 0 entryStackTop dpre (dmsg ++ dpost)).mp $$ Hdata
  isimp only [hdpre, hseg531] at Hdr1
  ihave ⟨Hdmsg, Hdpost⟩ :=
    (Slices.ByteSlice_append 0 1049107 dmsg dpost).mp $$ Hdr1
  isimp only [hdmsg, hseg549] at Hdpost
  -- the stack region that absolute `func 55` takes
  ihave ⟨Hbelow, %hbelowLength⟩ :=
    StackBelow_length frame decoderDepth lower $$ Hbelow
  have htake16 :
      (lower.take (decoderDepth - errorNewDepth)).length =
        decoderDepth - errorNewDepth := by
    rw [List.length_take, hbelowLength]
    omega
  ihave ⟨Hdeep1, Herrzone⟩ :=
    frame_split frame decoderDepth errorNewDepth lower (by decide) $$ Hbelow
  -- absolute `func 55` builds the `io::Error` at `frame + 16`
  simp only [trailingBuild, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (16 : UInt32) + frame = frame + 16 from UInt32.add_comm _ _]
  wasm_twp_pures [twp_const twp_const twp_const]
  have Hnew : Func52Spec (hlc := hlc) :=
    Project.RustHashMap.Func52Proof.func52_correct
  unfold Func52Spec CallContract callExpr at Hnew
  simp only [List.cons_append, List.nil_append] at Hnew
  iapply Hnew (sp := frame) (out := frame + 16) (kind := 12)
    (msgPtr := 1049107) (msgLen := 18) (heapId := heapId) (outBefore := errB)
    (below := lower.drop (decoderDepth - errorNewDepth)) (msgBytes := dmsg)
    (storedCursor := storedCursor) (frontier := frontier) (history := history)
    (input := input) (output := output) (raised := raised)
    (callerLocals :=
      { params := [.i32 out, v1, v2],
        locals := [.i32 frame, l4, l5], values := [] })
    (stack := stack)
  isplitl_exacts [Hruntime Hsp Herrzone Herr Hdmsg Hbump Hstreams]
  isplitl_pureexact
    ⟨herrLength, hE160, hout16, by decide, by decide,
      by rw [h18]; exact hdmsg⟩
  isplit
  · iintro %w0 %w1 %w2 %w3 %belowA %storedCursorA %frontierA %historyA
    iintro Hruntime Hsp Herrzone Herr Hdmsg Hbump Hstreams %hw0
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    -- the data segment, whole again
    ihave Hdr1 :=
      ByteSlice_glue 1049107 dmsg dpost 18 hdmsg $$ [Hdmsg Hdpost]
    · isplitl_exact Hdmsg
      · irw_exact [hseg549] with Hdpost
    ihave Hdata :=
      ByteSlice_glue entryStackTop dpre (dmsg ++ dpost) 531 hdpre $$
        [Hdpre Hdr1]
    · isplitl_exact Hdpre
      · irw_exact [hseg531] with Hdr1
    isimp only [← hdataShape] at Hdata
    -- the stack region, whole again
    ihave Hbelow :=
      frame_join frame decoderDepth errorNewDepth
        (lower.take (decoderDepth - errorNewDepth)) belowA htake16
        (by decide) $$ [Hdeep1 Herrzone]
    · isplitl_exact Hdeep1
      · iexact Herrzone
    -- the output slot, as five words
    obtain ⟨q0, q1, q2, q3, q4, houtShape⟩ :=
      five_word_bytes outBefore houtLength
    isimp only [houtShape] at Hout
    ihave ⟨H0, H1, H2, H3, H4⟩ :=
      five_words_of_ByteSlice out q0 q1 q2 q3 q4 $$ Hout
    -- the tag
    wasm_twp_pures [twp_localGet twp_const]
    ihave H0 := word_move out (out + 0) q0 hzero $$ H0
    wasm_twp_rebind twp_store32 (address := out) (offset := 0) q0
      hf0 hf0a hf0b hf0c with H0
    ihave H0 := word_move (out + 0) out 1 hzero.symm $$ H0
    -- the record, as two packed pairs
    ihave ⟨R0, R1, R2, R3⟩ :=
      four_words_of_ByteSlice (frame + 16) w0 w1 w2 w3 $$ Herr
    isimp only [g20, g24, g28] at R1 R2 R3
    ihave Rlo :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (frame + 16) w0 w1).mp $$ [R0 R1]
    · isplitl_exact R0
      · irw_exact [g20] with R1
    ihave Rhi :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (frame + 24) w2 w3).mp $$ [R2 R3]
    · isplitl_exact R2
      · irw_exact [g28] with R3
    -- the high pair of the output slot
    ihave Hpair12 :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (out + 12) q3 q4).mp $$ [H3 H4]
    · isplitl_exact H3
      · irw_exact [s16] with H4
    wasm_twp_block_move
      (frame, 24, w2.toUInt64 ||| (w3.toUInt64 <<< 32), hfa24)
      (out, 12, q3.toUInt64 ||| (q4.toUInt64 <<< 32), hfaO12)
      with Rhi Hpair12
    -- the low pair of the output slot
    ihave Hpair4 :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (out + 4) q1 q2).mp $$ [H1 H2]
    · isplitl_exact H1
      · irw_exact [s8] with H2
    wasm_twp_block_move
      (frame, 16, w0.toUInt64 ||| (w1.toUInt64 <<< 32), hfa16)
      (out, 4, q1.toUInt64 ||| (q2.toUInt64 <<< 32), hfaO4)
      with Rlo Hpair4
    -- the output slot, as bytes again
    ihave ⟨H3, H4⟩ :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (out + 12) w2 w3).mpr $$ Hpair12
    isimp only [s16] at H4
    ihave ⟨H1, H2⟩ :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (out + 4) w0 w1).mpr $$ Hpair4
    isimp only [s8] at H2
    ihave Hout :=
      ByteSlice_of_five_words out 1 w0 w1 w2 w3 houtNowrap $$
        [H0 H1 H2 H3 H4]
    · isplitl_exacts [H0 H1 H2 H3]
      iexact H4
    -- the record, whole again
    ihave ⟨R0, R1⟩ :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (frame + 16) w0 w1).mpr $$ Rlo
    ihave ⟨R2, R3⟩ :=
      (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
        (frame + 24) w2 w3).mpr $$ Rhi
    isimp only [← g24] at R2 R3
    isimp only [← g20] at R2 R3
    ihave Herr :=
      ByteSlice_of_four_words (frame + 16) w0 w1 w2 w3 hout16 $$
        [R0 R1 R2 R3]
    · isplitl_exacts [R0 R1 R2]
      iexact R3
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hnormal := Hnormal $$ %w0 %w1 %w2 %w3
      %(lower.take (decoderDepth - errorNewDepth) ++ belowA)
      %storedCursorA %frontierA %historyA
    iapply Hnormal $$ Hruntime Hsp Hbelow Herr Hout Hdata Hbump Hstreams
      %hw0
  · iintro %remaining' Hstreams
    ihave Hoom := BI.and_elim_r $$ Hcont
    ihave Hoom := Hoom $$ %remaining'
    iapply Hoom $$ Hstreams

/-! ## The epilogue -/

set_option maxHeartbeats 2000000 in
/-- The stack epilogue and the return.  The body raises the stack pointer
by 96 and gives the frame back to the caller. -/
private theorem twp_key_return [WasmSmallStepGS hlc Universal.State]
    (sp : UInt32) {p0 p1 p2 l4 l5 : Value}
    {lower frameBytes : List UInt8}
    {callerLocals : Locals} {stack : List Value} {code : Program}
    {arity : Nat} {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp} :
    iprop(
      RuntimeContext ∗
      StackPointer (sp - 96) ∗
      StackBelow (sp - 96) decoderDepth lower ∗
      Slices.ByteSlice 0 (sp - 96) frameBytes ∗
      ⌜frameBytes.length = 96 ∧ lower.length = decoderDepth⌝ ∗
      (∀ below' : List UInt8,
        RuntimeContext -∗
        StackPointer sp -∗
        StackBelow sp keyDecoderDepth below' -∗
        ResumeWP [] callerLocals stack code arity remainder controls calls
          s E Φ)) ⊢
      WP (.running
          ⟨⟨[p0, p1, p2], [.i32 (sp - 96), l4, l5], []⟩,
            keyEpilogue, 0, [], [],
            { locals := ⟨callerLocals.params, callerLocals.locals, stack⟩,
              continuation := code, resultArity := arity,
              callerRemainder := remainder, control := controls,
              returningInstance := ⟨0⟩ } :: calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hlower, Hframe, %hlengths, Hcont⟩
  obtain ⟨hframeLength, hlowerLength⟩ := hlengths
  have hbase96 : sp - UInt32.ofNat 96 = sp - 96 := rfl
  have hcut96 : keyDecoderDepth - 96 = decoderDepth := rfl
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  isimp only [StackPointer] at Hsp
  simp only [keyEpilogue]
  wasm_twp_pures [twp_localGet twp_const twp_add]
  rw [show (96 : UInt32) + (sp - 96) = sp by
    rw [UInt32.add_comm, UInt32.sub_add_cancel]]
  wasm_twp_rebind twp_globalSet with Hsp
  wasm_twp_rebind Wasm.SmallStep.twp_returnFromCallFallthrough with Hmodule
  simp only [List.take_zero, List.nil_append]
  ihave Hframe96 :=
    StackBelow_intro sp (sp - 96) 96 frameBytes hframeLength hbase96 $$
      Hframe
  isimp only [← hbase96, ← hcut96] at Hlower
  ihave Hbelow :=
    frame_join sp keyDecoderDepth 96 lower frameBytes
      (by rw [hcut96]; exact hlowerLength) (by decide) $$ [Hlower Hframe96]
  · isplitl_exact Hlower
    · iexact Hframe96
  ihave Hsp : StackPointer sp $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  iclose_map_runtime Hruntime with Hmodule Henv
  isimp only [ResumeWP, resumeExpr, List.nil_append] at Hcont
  ihave Hcont := Hcont $$ %(lower ++ frameBytes)
  iapply Hcont $$ Hruntime Hsp Hbelow

set_option maxHeartbeats 2000000 in
/-- The facts of an input that holds a key.  The first four bytes are the
key and the rest is the map. -/
private theorem key_input_facts (len : UInt32) (bytes : List UInt8)
    (hbytesLength : bytes.length = len.toNat)
    (hnot : ¬ len < (4 : UInt32)) :
    4 ≤ bytes.length ∧
      (mapBytes bytes).length = (len - 4).toNat ∧
      bytes.take 4 = WordCodec.u32le.serialize [leadingKey bytes] := by
  have h4 : (4 : UInt32).toNat = 4 := rfl
  have hfour : 4 ≤ len.toNat := by
    by_contra hc
    exact hnot (UInt32.lt_iff_toNat_lt.mpr (by rw [h4]; omega))
  have hle : (4 : UInt32) ≤ len :=
    UInt32.le_iff_toNat_le.mpr (by simpa using hfour)
  have hsub : (len - 4).toNat = len.toNat - 4 := by
    rw [UInt32.toNat_sub_of_le len 4 hle]
    rfl
  have hmap : (mapBytes bytes).length = (len - 4).toNat := by
    simp only [mapBytes, List.length_drop, hbytesLength, hsub]
  have hlen4 : (bytes.take 4).length = 4 := by
    rw [List.length_take]
    omega
  refine ⟨by omega, hmap, ?_⟩
  simp only [WordCodec.serialize_cons, WordCodec.serialize_nil,
    List.append_nil]
  exact (Slices.encodeU32_decodeU32_of_length (bytes.take 4) hlen4).symm

set_option maxHeartbeats 2000000 in
/-- The address facts of the header cell and of the decoder result slot. -/
private theorem key_slot_facts (frame : UInt32)
    (hframeNowrap : frame.toNat + 96 < UInt32.size) :
    (frame + 32).toNat + 16 < UInt32.size ∧
      (frame + 8).toNat + 8 < UInt32.size ∧
      frame.toNat + 32 + 4 ≤ UInt32.size ∧
      frame.toNat + 36 + 4 ≤ UInt32.size ∧
      frame.toNat + 40 + 8 ≤ UInt32.size := by
  obtain ⟨a8, a12, a16, a32, a48, a52, a56, a60, a64, a72, a76, a80, a84,
    a92⟩ := frame_addr_facts frame hframeNowrap
  refine ⟨by omega, by omega, by omega, by omega, by omega⟩

/-- Read the bound of a byte slice without giving the slice up. -/
private theorem ByteSlice_bound [WasmHeapGS Universal.State]
    (ptr : UInt32) (bytes : List UInt8) :
    Slices.ByteSlice (α := Universal.State) 0 ptr bytes ⊢
      iprop(Slices.ByteSlice 0 ptr bytes ∗
        ⌜ptr.toNat + bytes.length < UInt32.size⌝) := by
  iintro Hbytes
  unfold Slices.ByteSlice
  icases Hbytes with ⟨%hnowrap, Hraw⟩
  isplitl [Hraw]
  · isplitl_pureexact hnowrap
    iexact Hraw
  · ipureexact hnowrap

/-- The first word of a byte slice has room. -/
private theorem ptr_slot_bound (ptr : UInt32) (n : Nat)
    (hbound : ptr.toNat + n < UInt32.size) (hle : 4 ≤ n) :
    ptr.toNat + 0 + 4 ≤ UInt32.size ∧ ptr.toNat + 4 < UInt32.size := by
  omega

set_option maxHeartbeats 2000000 in
/-- The arithmetic of the frame base.  The stack pointer is at least the
depth of the body, so the frame and its cells do not wrap. -/
private theorem key_frame_facts (sp : UInt32)
    (hspLow : keyDecoderDepth ≤ sp.toNat) :
    (sp - 96).toNat = sp.toNat - 96 ∧
      decoderDepth ≤ (sp - 96).toNat ∧
      (sp - 96).toNat + 96 < UInt32.size ∧
      ((sp - 96) + 8).toNat + 4 < UInt32.size ∧
      ((sp - 96) + 12).toNat + 4 < UInt32.size ∧
      ((sp - 96) + 72).toNat + 4 < UInt32.size ∧
      (sp - 96).toNat + 8 + 4 ≤ UInt32.size ∧
      (sp - 96).toNat + 12 + 4 ≤ UInt32.size := by
  have hkeyD : keyDecoderDepth = 336 := rfl
  have hdeepD : decoderDepth = 240 := rfl
  have hsize32 : UInt32.size = 4294967296 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hspNat : (336 : Nat) ≤ sp.toNat := by
    rw [hkeyD] at hspLow; exact hspLow
  have hframeNat : (sp - 96).toNat = sp.toNat - 96 := by
    rw [UInt32.toNat_sub_of_le sp 96
      (UInt32.le_iff_toNat_le.mpr
        (by simpa using (by omega : (96 : Nat) ≤ sp.toNat)))]
    rfl
  have hnowrap : (sp - 96).toNat + 96 < UInt32.size := by omega
  obtain ⟨a8, a12, _a16, _a32, _a48, _a52, _a56, _a60, _a64, a72, _a76,
    _a80, _a84, _a92⟩ := frame_addr_facts (sp - 96) hnowrap
  refine ⟨hframeNat, by omega, hnowrap, by omega, by omega, by omega,
    by omega, by omega⟩

private theorem func7_index :
    Project.RustHashMap.«module».funcs[7]? =
      some Project.RustHashMap.func7Def := by rfl

set_option maxHeartbeats 2000000 in
/-- The key-and-map decoder body meets its contract. -/
theorem func7_correct [WasmSmallStepGS hlc Universal.State] :
    Func7Spec (hlc := hlc) := by
  unfold Func7Spec CallContract callExpr
  intro sp out ptr len heapId bytes outBefore below dataBytes storedCursor
    frontier history input output raised callerLocals stack code arity
    remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hbytes, Hdata, Hbump, Hstreams,
    %hfacts, Hcont⟩
  obtain ⟨houtLength, hbytesLength, hspLow, houtNowrap, hdataLength⟩ :=
    hfacts
  -- arithmetic on the frame base
  have hdeepD : decoderDepth = 240 := rfl
  have hbase96 : sp - UInt32.ofNat 96 = sp - 96 := rfl
  have hcut96 : keyDecoderDepth - 96 = decoderDepth := rfl
  obtain ⟨hframeNat, hframeLow, hframeNowrap, n8, n12, n72, d8, d12⟩ :=
    key_frame_facts sp hspLow
  obtain ⟨a8, a12, a16, a32, a48, a52, a56, a60, a64, a72, a76, a80, a84,
    a92⟩ := frame_addr_facts (sp - 96) hframeNowrap
  obtain ⟨hf8, hf8a, hf8b, hf8c⟩ := offset_facts (sp - 96) 8 8 rfl d8
  obtain ⟨hf12, hf12a, hf12b, hf12c⟩ :=
    offset_facts (sp - 96) 12 12 rfl d12
  -- the call and the frame prologue
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 10
      Project.RustHashMap.func7Def (by decide) func7_index with Hmodule
  simp [Project.RustHashMap.func7Def, Function.toLocals, Function.numParams]
  rw [func7_shape]
  iclose_map_runtime Hruntime with Hmodule Henv
  isimp only [StackPointer] at Hsp
  simp only [keyPrologue, List.cons_append, List.nil_append]
  wasm_twp_rebind twp_globalGet with Hsp
  wasm_twp_pures [twp_const twp_sub]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_rebind twp_globalSet with Hsp
  ihave Hsp : StackPointer (sp - 96) $$ [Hsp]
  · unfold StackPointer
    iexact Hsp
  -- the stack region below and the ten cells of the frame
  ihave ⟨Hlower, Hframe⟩ :=
    frame_split sp keyDecoderDepth 96 below (by decide) $$ Hbelow
  isimp only [hcut96, hbase96] at Hlower Hframe
  ihave ⟨%hframeLength, Hframe⟩ :=
    StackBelow_base sp (sp - 96) 96 (below.drop decoderDepth) hbase96 $$
      Hframe
  have hbelowLen : below.length = 336 := by
    have h : (below.drop decoderDepth).length = 96 := hframeLength
    rw [List.length_drop] at h
    omega
  have hlowerLen : (below.take decoderDepth).length = decoderDepth := by
    have h : (below.take decoderDepth).length =
        min decoderDepth below.length := List.length_take
    rw [hbelowLen] at h
    omega
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, hqShape, hq0, hq1, hq2,
    hq3, hq4, hq5, hq6, hq7, hq8, hq9⟩ :=
    frame_pieces (below.drop decoderDepth) hframeLength
  isimp only [hqShape] at Hframe
  ihave ⟨Hq0, Hq1, Hq2, Hq3, Hq4, Hq5, Hq6, Hq7, Hq8, Hq9⟩ :=
    frame_cut (sp - 96) q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 hq0 hq1 hq2 hq3 hq4
      hq5 hq6 hq7 hq8 $$ Hframe
  obtain ⟨u1, hu1⟩ := word_bytes q1 hq1
  obtain ⟨u2, hu2⟩ := word_bytes q2 hq2
  obtain ⟨u7, hu7⟩ := word_bytes q7 hq7
  isimp only [hu1] at Hq1
  isimp only [hu2] at Hq2
  isimp only [hu7] at Hq7
  ihave Hq1 := one_word_of_ByteSlice ((sp - 96) + 8) u1 $$ Hq1
  ihave Hq2 := one_word_of_ByteSlice ((sp - 96) + 12) u2 $$ Hq2
  ihave Hq7 := one_word_of_ByteSlice ((sp - 96) + 72) u7 $$ Hq7
  -- the slice header goes into the frame
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := sp - 96) (offset := 12) u2
    hf12 hf12a hf12b hf12c with Hq2
  wasm_twp_pures [twp_localGet twp_localGet]
  wasm_twp_rebind twp_store32 (address := sp - 96) (offset := 8) u1
    hf8 hf8a hf8b hf8c with Hq1
  -- the five blocks
  iapply twp_block
  simp only [body1]
  iapply twp_block
  simp only [body2]
  iapply twp_block
  simp only [body3]
  iapply twp_block
  simp only [body4]
  iapply twp_block
  simp only [guardBody]
  wasm_twp_pures [twp_localGet twp_const]
  by_cases hshort : len < (4 : UInt32)
  · -- the input is shorter than one key
    have hnotAccept : ¬ KeyDecodeAccepts bytes := by
      intro haccept
      have hfour : 4 ≤ bytes.length := haccept.1
      have hlt : len.toNat < (4 : UInt32).toNat :=
        UInt32.lt_iff_toNat_lt.mp hshort
      have h4 : (4 : UInt32).toNat = 4 := rfl
      omega
    iapply twp_ltU (result := 1) (by rw [if_pos hshort])
    iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    simp only [shortArm]
    iapply twp_short_build out ptr len (sp - 96) heapId q5 q6 q9 dataBytes
      (below.take decoderDepth) u7 storedCursor frontier history input
      output raised ValueType.i32.zero ValueType.i64.zero hq5 hq6 hq9
      hdataLength hframeLow hframeNowrap
    isplitl_exacts [Hruntime Hsp Hlower Hq5 Hq6 Hq7 Hq9 Hdata Hbump
      Hstreams]
    isplit
    · iintro %v0 %v1 %v2 %v3 %w1 %w2 %w3 %errAfter %lower1 %cursor1
        %frontier1 %history1
      iintro Hruntime Hsp Hlower Hq5 Hq6 Hq7 Hq9 Hdata Hbump Hstreams
        %hvFacts
      obtain ⟨hv0, hafterLength⟩ := hvFacts
      iapply twp_br (by rfl)
      simp only [List.take_zero, List.nil_append]
      simp only [rejectWrite]
      iapply twp_reject_stores out v0 v1 v2 v3 (sp - 96) outBefore
        (.i32 0) houtLength houtNowrap
      isplitl_exact Hout
      iintro Hout
      iapply twp_br (by rfl)
      simp only [List.take_zero, List.nil_append]
      -- the frame is whole again
      ihave Hq1 := ByteSlice_of_one_word ((sp - 96) + 8) ptr n8 $$ Hq1
      ihave Hq2 := ByteSlice_of_one_word ((sp - 96) + 12) len n12 $$ Hq2
      ihave Hq7 := ByteSlice_of_one_word ((sp - 96) + 72) w3 n72 $$ Hq7
      ihave Hframe :=
        frame_glue (sp - 96) q0 (WordCodec.u32le.serialize [ptr])
          (WordCodec.u32le.serialize [len]) q3 q4
          (WordCodec.u32le.serialize [v0, v1, v2, v3])
          (WordCodec.u32le.serialize [w1, w2])
          (WordCodec.u32le.serialize [w3]) q8 errAfter hq0
          (ser_one_length ptr) (ser_one_length len) hq3 hq4
          (ser_four_length v0 v1 v2 v3) (ser_two_length w1 w2)
          (ser_one_length w3) hq8 $$
          [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8 Hq9]
      · isplitl_exacts [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8]
        iexact Hq9
      ihave ⟨Hlower, %hlower1Len⟩ :=
        StackBelow_length (sp - 96) decoderDepth lower1 $$ Hlower
      iapply twp_key_return sp
      isplitl_exacts [Hruntime Hsp Hlower Hframe]
      isplitl_pureexact
        ⟨by simp only [List.length_append, hq0, hq3, hq4, hq8,
            hafterLength, ser_one_length, ser_two_length,
            ser_four_length], hlower1Len⟩
      iintro %below' Hruntime Hsp Hbelow
      wasm_serialize_norm at Hout
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hreject := BI.and_elim_l $$ Htail
      ihave Hreject := Hreject $$ %v0 %v1 %v2 %v3 %below' %cursor1
        %frontier1 %history1
      iapply Hreject $$ %hnotAccept Hruntime Hsp Hbelow Hout Hbytes Hdata
        Hbump Hstreams %hv0
    · iintro %remaining' Hstreams
      ihave Htail := BI.and_elim_r $$ Hcont
      ihave Hoom := BI.and_elim_r $$ Htail
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams
  · -- the input holds a key in front of the map
    obtain ⟨hfourBytes, hmapLen, htakeKey⟩ :=
      key_input_facts len bytes hbytesLength hshort
    obtain ⟨hout32, hhdr8, b32, b36, b40⟩ :=
      key_slot_facts (sp - 96) hframeNowrap
    obtain ⟨hf32, hf32a, hf32b, hf32c⟩ :=
      offset_facts (sp - 96) 32 32 rfl b32
    obtain ⟨hf36, hf36a, hf36b, hf36c⟩ :=
      offset_facts (sp - 96) 36 36 rfl b36
    have hfa40 := offset_facts64 (sp - 96) 40 40 rfl b40
    have hokTag : okTag = (2147483649 : UInt32) := rfl
    have hofs4 : ptr + UInt32.ofNat 4 = ptr + 4 := rfl
    have hmb : bytes.drop 4 = mapBytes bytes := rfl
    have hzero : ptr + (0 : UInt32) = ptr := UInt32.add_zero ptr
    have g12 : (sp - 96) + (8 : UInt32) + 4 = (sp - 96) + 12 := by
      rw [UInt32.add_assoc, show (8 : UInt32) + 4 = 12 from by decide]
    have c36 : (sp - 96) + (32 : UInt32) + 4 = (sp - 96) + 36 := by
      rw [UInt32.add_assoc, show (32 : UInt32) + 4 = 36 from by decide]
    have c40 : (sp - 96) + (36 : UInt32) + 4 = (sp - 96) + 40 := by
      rw [UInt32.add_assoc, show (36 : UInt32) + 4 = 40 from by decide]
    have c44 : (sp - 96) + (40 : UInt32) + 4 = (sp - 96) + 44 := by
      rw [UInt32.add_assoc, show (40 : UInt32) + 4 = 44 from by decide]
    ihave ⟨Hbytes, %hptrBound⟩ := ByteSlice_bound ptr bytes $$ Hbytes
    obtain ⟨hbptr, hptr4⟩ :=
      ptr_slot_bound ptr bytes.length hptrBound hfourBytes
    obtain ⟨hk0, hk1, hk2, hk3⟩ := offset_facts ptr 0 0 rfl hbptr
    rw [hzero] at hk1 hk2 hk3
    iapply twp_ltU (result := 0) (by rw [if_neg hshort])
    iapply twp_brIfZero
    -- the header moves past the key
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    rw [show (4294967292 : UInt32) + len = len - 4 from
      (UInt32.add_comm _ _).trans (sub_four len)]
    wasm_twp_rebind twp_store32 (address := sp - 96) (offset := 12) len
      hf12 hf12a hf12b hf12c with Hq2
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
    rw [show (4 : UInt32) + ptr = ptr + 4 from UInt32.add_comm _ _]
    wasm_twp_rebind twp_store32 (address := sp - 96) (offset := 8) ptr
      hf8 hf8a hf8b hf8c with Hq1
    -- the key comes out of the first four bytes
    ihave ⟨Hkey, Hmap⟩ := ByteSlice_cut ptr bytes 4 hfourBytes $$ Hbytes
    isimp only [htakeKey] at Hkey
    isimp only [hofs4] at Hmap
    isimp only [hmb] at Hmap
    ihave Hkey := one_word_of_ByteSlice ptr (leadingKey bytes) $$ Hkey
    wasm_twp_pures [twp_localGet]
    wasm_twp_rebind twp_load32_addr (leadingKey bytes) hk1 hk2 hk3
      with Hkey
    wasm_twp_localSet
    iapply twp_br (by rfl)
    simp only [List.take_zero, List.drop_zero, List.nil_append]
    simp only [decodePart, decodeCheck,
      List.cons_append, List.nil_append]
    -- absolute `func 4` reads the map
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (32 : UInt32) + (sp - 96) = sp - 96 + 32 from
      UInt32.add_comm _ _]
    wasm_twp_pures [twp_localGet twp_const twp_add]
    rw [show (8 : UInt32) + (sp - 96) = sp - 96 + 8 from
      UInt32.add_comm _ _]
    isimp only [← g12] at Hq2
    have Hdec : Func1Spec (hlc := hlc) :=
      Project.RustHashMap.Func1Proof.func1_correct
    unfold Func1Spec CallContract callExpr at Hdec
    simp only [List.cons_append, List.nil_append] at Hdec
    iapply Hdec (sp := sp - 96) (out := sp - 96 + 32)
      (hdr := sp - 96 + 8) (ptr := ptr + 4) (len := len - 4)
      (heapId := heapId) (bytes := mapBytes bytes) (outBefore := q4)
      (below := below.take decoderDepth) (dataBytes := dataBytes)
      (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        { params := [.i32 out, .i32 ptr, .i32 len],
          locals := [.i32 (sp - 96), .i32 (leadingKey bytes),
            ValueType.i64.zero], values := [] })
      (stack := [])
    isplitl_exacts [Hruntime Hsp Hlower Hq4 Hq1 Hq2 Hmap Hdata Hbump
      Hstreams]
    isplitl_pureexact
      ⟨hq4, hmapLen, hframeLow, hout32, hhdr8, hdataLength⟩
    isplit
    · iintro %capacity %buffer %payload %spare %belowD %cursorD %frontierD
        %historyD
      iintro %hAccept Hruntime Hsp Hlower Hq4 Hq1 Hq2 Hmap Hdata Hbuf
        Hbump Hstreams %hpFacts
      obtain ⟨hpayload, hcapLe, hspareLen, hcapZero, halign⟩ := hpFacts
      have hkp : keyPayload bytes = payload := by rw [hpayload]; rfl
      isimp only [← hkp] at Hbuf
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      isimp only [g12] at Hq2
      have hiff :=
        remaining_eq_zero_iff (mapBytes bytes) (len - 4) hmapLen hAccept
      -- the four words of the decoder result
      ihave ⟨Hr0, Hr1, Hr2, Hr3⟩ :=
        ByteSlice_four_words ((sp - 96) + 32) okTag capacity buffer
          (headerWord (mapBytes bytes)) $$ Hq4
      isimp only [c36] at Hr1
      isimp only [c36, c40] at Hr2
      isimp only [c36, c40, c44] at Hr3
      wasm_twp_pures [twp_localGet]
      ihave Hpair :=
        (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
          ((sp - 96) + 40) buffer (headerWord (mapBytes bytes))).mp $$
          [Hr2 Hr3]
      · isplitl_exact Hr2
        · irw_exact [← c44] with Hr3
      wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := sp - 96)
        (offset := 40)
        (buffer.toUInt64 |||
          ((headerWord (mapBytes bytes)).toUInt64 <<< 32))
        hfa40.1 hfa40.2.1 hfa40.2.2.1 hfa40.2.2.2.1 hfa40.2.2.2.2.1
        hfa40.2.2.2.2.2.1 hfa40.2.2.2.2.2.2.1 hfa40.2.2.2.2.2.2.2
        with Hpair
      wasm_twp_localSet
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := sp - 96) (offset := 36)
        capacity hf36 hf36a hf36b hf36c with Hr1
      wasm_twp_localSet
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := sp - 96) (offset := 32) okTag
        hf32 hf32a hf32b hf32c with Hr0
      wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      wasm_twp_pures [twp_const]
      have hokNe : ¬ (okTag ≠ (2147483649 : UInt32)) := by
        intro h
        exact h hokTag
      iapply twp_ne (result := 0) (by rw [if_neg hokNe])
      iapply twp_brIfZero
      -- the buffer address goes to its local
      wasm_twp_pures [twp_localGet twp_wrapI64]
      rw [wrap_low buffer (headerWord (mapBytes bytes))]
      wasm_twp_localSet
      wasm_twp_pures [twp_localGet]
      wasm_twp_rebind twp_load32 (address := sp - 96) (offset := 12)
        (len - 4 - 4 - 8 * headerWord (mapBytes bytes))
        hf12 hf12a hf12b hf12c with Hq2
      ihave ⟨Hlower, %hlowerDLen⟩ :=
        StackBelow_length (sp - 96) decoderDepth belowD $$ Hlower
      by_cases hrem :
        (len - 4 - 4 - 8 * headerWord (mapBytes bytes)) = 0
      · -- the decoder read the whole map
        have hacc : KeyDecodeAccepts bytes :=
          ⟨hfourBytes, hAccept, (hiff.mp hrem).symm⟩
        iapply twp_eqz (result := 1) (by rw [if_pos hrem])
        iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.nil_append]
        rw [show okWrite = okWrite ++ ([] : Program) from
          (List.append_nil okWrite).symm]
        iapply twp_ok_write out buffer capacity (leadingKey bytes)
          (headerWord (mapBytes bytes)) (sp - 96) outBefore houtLength
          houtNowrap (code := [])
        isplitl_exact Hout
        iintro Hout
        wasm_twp_pures [twp_exitControl]
        dsimp only
        simp only [List.take_zero, List.nil_append]
        -- the input, whole again
        ihave Hkey :=
          ByteSlice_of_one_word ptr (leadingKey bytes) hptr4 $$ Hkey
        isimp only [← hofs4] at Hmap
        ihave Hbytes :=
          ByteSlice_glue ptr (WordCodec.u32le.serialize [leadingKey bytes])
            (mapBytes bytes) 4 (ser_one_length (leadingKey bytes)) $$
            [Hkey Hmap]
        · isplitl_exact Hkey
          · iexact Hmap
        isimp only [← htakeKey, mapBytes, List.take_append_drop] at Hbytes
        -- the frame, whole again
        ihave ⟨Hr2, Hr3⟩ :=
          (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
            ((sp - 96) + 40) buffer (headerWord (mapBytes bytes))).mpr $$
            Hpair
        isimp only [← c36] at Hr1
        isimp only [← c36, ← c40] at Hr2
        isimp only [← c36, ← c40, ← c44] at Hr3
        ihave Hq4 :=
          ByteSlice_of_four_words ((sp - 96) + 32) okTag capacity buffer
            (headerWord (mapBytes bytes)) hout32 $$ [Hr0 Hr1 Hr2 Hr3]
        · isplitl_exacts [Hr0 Hr1 Hr2]
          iexact Hr3
        ihave Hq1 :=
          ByteSlice_of_one_word ((sp - 96) + 8)
            (ptr + 4 + 4 + 8 * headerWord (mapBytes bytes)) n8 $$ Hq1
        ihave Hq2 :=
          ByteSlice_of_one_word ((sp - 96) + 12)
            (len - 4 - 4 - 8 * headerWord (mapBytes bytes)) n12 $$ Hq2
        ihave Hq7 := ByteSlice_of_one_word ((sp - 96) + 72) u7 n72 $$ Hq7
        ihave Hframe :=
          frame_glue (sp - 96) q0
            (WordCodec.u32le.serialize
              [ptr + 4 + 4 + 8 * headerWord (mapBytes bytes)])
            (WordCodec.u32le.serialize
              [len - 4 - 4 - 8 * headerWord (mapBytes bytes)])
            q3
            (WordCodec.u32le.serialize
              [okTag, capacity, buffer, headerWord (mapBytes bytes)])
            q5 q6 (WordCodec.u32le.serialize [u7]) q8 q9 hq0
            (ser_one_length _) (ser_one_length _) hq3
            (ser_four_length _ _ _ _) hq5 hq6 (ser_one_length u7) hq8 $$
            [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8 Hq9]
        · isplitl_exacts [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8]
          iexact Hq9
        iapply twp_key_return sp
        isplitl_exacts [Hruntime Hsp Hlower Hframe]
        isplitl_pureexact
          ⟨by simp only [List.length_append, hq0, hq3, hq5, hq6, hq8, hq9,
              ser_one_length, ser_four_length], hlowerDLen⟩
        iintro %below' Hruntime Hsp Hbelow
        wasm_serialize_norm at Hout
        ihave Hok := BI.and_elim_l $$ Hcont
        isimp only [pairCount] at Hok
        ihave Hok := Hok $$ %capacity %buffer %spare %below' %cursorD
          %frontierD %historyD
        iapply Hok $$ %hacc Hruntime Hsp Hbelow Hout Hbytes Hdata Hbuf
          Hbump Hstreams %⟨hcapLe, hspareLen, hcapZero, halign⟩
      · -- the input holds bytes after the map
        have hnotAccept : ¬ KeyDecodeAccepts bytes := by
          intro hacc
          exact hrem (hiff.mpr hacc.2.2.symm)
        iapply twp_eqz (result := 0) (by rw [if_neg hrem])
        iapply twp_brIfZero
        iapply twp_trailing_error out (sp - 96) (.i32 buffer)
          (.i32 capacity) heapId q3 outBefore dataBytes belowD cursorD
          frontierD historyD input output raised (.i32 (leadingKey bytes))
          (.i64 (buffer.toUInt64 |||
            ((headerWord (mapBytes bytes)).toUInt64 <<< 32)))
          hq3 houtLength hdataLength houtNowrap hframeLow hframeNowrap
        isplitl_exacts [Hruntime Hsp Hlower Hq3 Hout Hdata Hbump Hstreams]
        isplit
        · iintro %w0 %w1 %w2 %w3 %belowE %cursorE %frontierE %historyE
          iintro Hruntime Hsp Hlower Hq3 Hout Hdata Hbump Hstreams %hw0
          simp only [trailingFree]
          ihave ⟨Hlower, %hlowerELen⟩ :=
            StackBelow_length (sp - 96) decoderDepth belowE $$ Hlower
          iclear Hbuf
          -- the input, whole again
          ihave Hkey :=
            ByteSlice_of_one_word ptr (leadingKey bytes) hptr4 $$ Hkey
          isimp only [← hofs4] at Hmap
          ihave Hbytes :=
            ByteSlice_glue ptr
              (WordCodec.u32le.serialize [leadingKey bytes])
              (mapBytes bytes) 4 (ser_one_length (leadingKey bytes)) $$
              [Hkey Hmap]
          · isplitl_exact Hkey
            · iexact Hmap
          isimp only [← htakeKey, mapBytes, List.take_append_drop] at Hbytes
          -- the frame, whole again
          ihave ⟨Hr2, Hr3⟩ :=
            (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
              ((sp - 96) + 40) buffer (headerWord (mapBytes bytes))).mpr $$
              Hpair
          isimp only [← c36] at Hr1
          isimp only [← c36, ← c40] at Hr2
          isimp only [← c36, ← c40, ← c44] at Hr3
          ihave Hq4 :=
            ByteSlice_of_four_words ((sp - 96) + 32) okTag capacity buffer
              (headerWord (mapBytes bytes)) hout32 $$ [Hr0 Hr1 Hr2 Hr3]
          · isplitl_exacts [Hr0 Hr1 Hr2]
            iexact Hr3
          ihave Hq1 :=
            ByteSlice_of_one_word ((sp - 96) + 8)
              (ptr + 4 + 4 + 8 * headerWord (mapBytes bytes)) n8 $$ Hq1
          ihave Hq2 :=
            ByteSlice_of_one_word ((sp - 96) + 12)
              (len - 4 - 4 - 8 * headerWord (mapBytes bytes)) n12 $$ Hq2
          ihave Hq7 := ByteSlice_of_one_word ((sp - 96) + 72) u7 n72 $$ Hq7
          ihave Hframe :=
            frame_glue (sp - 96) q0
              (WordCodec.u32le.serialize
                [ptr + 4 + 4 + 8 * headerWord (mapBytes bytes)])
              (WordCodec.u32le.serialize
                [len - 4 - 4 - 8 * headerWord (mapBytes bytes)])
              (WordCodec.u32le.serialize [w0, w1, w2, w3])
              (WordCodec.u32le.serialize
                [okTag, capacity, buffer, headerWord (mapBytes bytes)])
              q5 q6 (WordCodec.u32le.serialize [u7]) q8 q9 hq0
              (ser_one_length _) (ser_one_length _)
              (ser_four_length _ _ _ _) (ser_four_length _ _ _ _) hq5 hq6
              (ser_one_length u7) hq8 $$
              [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8 Hq9]
          · isplitl_exacts [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8]
            iexact Hq9
          wasm_twp_pures [twp_localGet]
          by_cases hcap : capacity = 0
          · -- the map has no buffer to give back
            iapply twp_eqz (result := 1) (by rw [if_pos hcap])
            iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
            simp only [List.take_zero, List.nil_append]
            iapply twp_key_return sp
            isplitl_exacts [Hruntime Hsp Hlower Hframe]
            isplitl_pureexact
              ⟨by simp only [List.length_append, hq0, hq5, hq6, hq8, hq9,
                  ser_one_length, ser_four_length], hlowerELen⟩
            iintro %below' Hruntime Hsp Hbelow
            wasm_serialize_norm at Hout
            ihave Htail := BI.and_elim_r $$ Hcont
            ihave Hreject := BI.and_elim_l $$ Htail
            ihave Hreject := Hreject $$ %w0 %w1 %w2 %w3 %below' %cursorE
              %frontierE %historyE
            iapply Hreject $$ %hnotAccept Hruntime Hsp Hbelow Hout Hbytes
              Hdata Hbump Hstreams %hw0
          · -- the map gives its buffer back
            iapply twp_eqz (result := 0) (by rw [if_neg hcap])
            iapply twp_brIfZero
            wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl
              twp_const]
            have Hfree : Func57NoopSpec (hlc := hlc) :=
              Project.RustHashMap.DeallocNoop.func57_noop_correct
            unfold Func57NoopSpec CallContract callExpr at Hfree
            simp only [List.cons_append, List.nil_append] at Hfree
            iapply Hfree (ptr := buffer)
              (size := capacity <<< (3 % 32)) (alignment := 4)
              (callerLocals :=
                { params := [.i32 out, .i32 buffer, .i32 capacity],
                  locals := [.i32 (sp - 96), .i32 (leadingKey bytes),
                    .i64 (buffer.toUInt64 |||
                      ((headerWord (mapBytes bytes)).toUInt64 <<< 32))],
                  values := [] })
              (stack := [])
            isplitl_exact Hruntime
            iintro Hruntime
            isimp only [ResumeWP, resumeExpr, List.nil_append]
            iapply twp_br (by rfl)
            simp only [List.take_zero, List.nil_append]
            iapply twp_key_return sp
            isplitl_exacts [Hruntime Hsp Hlower Hframe]
            isplitl_pureexact
              ⟨by simp only [List.length_append, hq0, hq5, hq6, hq8, hq9,
                  ser_one_length, ser_four_length], hlowerELen⟩
            iintro %below' Hruntime Hsp Hbelow
            wasm_serialize_norm at Hout
            ihave Htail := BI.and_elim_r $$ Hcont
            ihave Hreject := BI.and_elim_l $$ Htail
            ihave Hreject := Hreject $$ %w0 %w1 %w2 %w3 %below' %cursorE
              %frontierE %historyE
            iapply Hreject $$ %hnotAccept Hruntime Hsp Hbelow Hout Hbytes
              Hdata Hbump Hstreams %hw0
        · iintro %remaining' Hstreams
          ihave Htail := BI.and_elim_r $$ Hcont
          ihave Hoom := BI.and_elim_r $$ Htail
          ihave Hoom := Hoom $$ %remaining'
          iapply Hoom $$ Hstreams
    · isplit
      · iintro %word0 %word1 %word2 %word3 %ptrD %lenD %belowD %cursorD
          %frontierD %historyD
        iintro %hNotDec Hruntime Hsp Hlower Hq4 Hq1 Hq2 Hmap Hdata Hbump
          Hstreams %hword0
        have hnotAccept : ¬ KeyDecodeAccepts bytes := by
          intro hacc
          exact hNotDec hacc.2.1
        have hword0' : word0 ≠ (2147483649 : UInt32) := by
          rw [← hokTag]; exact hword0
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        isimp only [g12] at Hq2
        ihave ⟨Hlower, %hlowerDLen⟩ :=
          StackBelow_length (sp - 96) decoderDepth belowD $$ Hlower
        -- the four words of the decode error
        ihave ⟨Hr0, Hr1, Hr2, Hr3⟩ :=
          ByteSlice_four_words ((sp - 96) + 32) word0 word1 word2 word3 $$
            Hq4
        isimp only [c36] at Hr1
        isimp only [c36, c40] at Hr2
        isimp only [c36, c40, c44] at Hr3
        wasm_twp_pures [twp_localGet]
        ihave Hpair :=
          (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
            ((sp - 96) + 40) word2 word3).mp $$ [Hr2 Hr3]
        · isplitl_exact Hr2
          · irw_exact [← c44] with Hr3
        wasm_twp_rebind Wasm.SmallStep.twp_load64 (address := sp - 96)
          (offset := 40) (word2.toUInt64 ||| (word3.toUInt64 <<< 32))
          hfa40.1 hfa40.2.1 hfa40.2.2.1 hfa40.2.2.2.1 hfa40.2.2.2.2.1
          hfa40.2.2.2.2.2.1 hfa40.2.2.2.2.2.2.1 hfa40.2.2.2.2.2.2.2
          with Hpair
        wasm_twp_localSet
        wasm_twp_pures [twp_localGet]
        wasm_twp_rebind twp_load32 (address := sp - 96) (offset := 36)
          word1 hf36 hf36a hf36b hf36c with Hr1
        wasm_twp_localSet
        wasm_twp_pures [twp_localGet]
        wasm_twp_rebind twp_load32 (address := sp - 96) (offset := 32)
          word0 hf32 hf32a hf32b hf32c with Hr0
        wasm_twp_localTee [List.length_cons, List.length_nil,
          Nat.reduceAdd, Nat.reduceSub, List.set]
        wasm_twp_pures [twp_const]
        iapply twp_ne (result := 1) (by rw [if_pos hword0'])
        iapply twp_brIf (by decide : (1 : UInt32) ≠ 0) (by rfl)
        simp only [List.take_zero, List.nil_append]
        simp only [rejectWrite]
        iapply twp_reject_stores out word0 word1 word2 word3 (sp - 96)
          outBefore (.i32 (leadingKey bytes)) houtLength houtNowrap
        isplitl_exact Hout
        iintro Hout
        iapply twp_br (by rfl)
        simp only [List.take_zero, List.nil_append]
        -- the input, whole again
        ihave Hkey :=
          ByteSlice_of_one_word ptr (leadingKey bytes) hptr4 $$ Hkey
        isimp only [← hofs4] at Hmap
        ihave Hbytes :=
          ByteSlice_glue ptr (WordCodec.u32le.serialize [leadingKey bytes])
            (mapBytes bytes) 4 (ser_one_length (leadingKey bytes)) $$
            [Hkey Hmap]
        · isplitl_exact Hkey
          · iexact Hmap
        isimp only [← htakeKey, mapBytes, List.take_append_drop] at Hbytes
        -- the frame, whole again
        ihave ⟨Hr2, Hr3⟩ :=
          (Project.RustHashMap.ReadAll.pointsTo_u32_pair_as_u64
            ((sp - 96) + 40) word2 word3).mpr $$ Hpair
        isimp only [← c36] at Hr1
        isimp only [← c36, ← c40] at Hr2
        isimp only [← c36, ← c40, ← c44] at Hr3
        ihave Hq4 :=
          ByteSlice_of_four_words ((sp - 96) + 32) word0 word1 word2 word3
            hout32 $$ [Hr0 Hr1 Hr2 Hr3]
        · isplitl_exacts [Hr0 Hr1 Hr2]
          iexact Hr3
        ihave Hq1 := ByteSlice_of_one_word ((sp - 96) + 8) ptrD n8 $$ Hq1
        ihave Hq2 := ByteSlice_of_one_word ((sp - 96) + 12) lenD n12 $$ Hq2
        ihave Hq7 := ByteSlice_of_one_word ((sp - 96) + 72) u7 n72 $$ Hq7
        ihave Hframe :=
          frame_glue (sp - 96) q0 (WordCodec.u32le.serialize [ptrD])
            (WordCodec.u32le.serialize [lenD]) q3
            (WordCodec.u32le.serialize [word0, word1, word2, word3])
            q5 q6 (WordCodec.u32le.serialize [u7]) q8 q9 hq0
            (ser_one_length ptrD) (ser_one_length lenD) hq3
            (ser_four_length _ _ _ _) hq5 hq6 (ser_one_length u7) hq8 $$
            [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8 Hq9]
        · isplitl_exacts [Hq0 Hq1 Hq2 Hq3 Hq4 Hq5 Hq6 Hq7 Hq8]
          iexact Hq9
        iapply twp_key_return sp
        isplitl_exacts [Hruntime Hsp Hlower Hframe]
        isplitl_pureexact
          ⟨by simp only [List.length_append, hq0, hq3, hq5, hq6, hq8, hq9,
              ser_one_length, ser_four_length], hlowerDLen⟩
        iintro %below' Hruntime Hsp Hbelow
        wasm_serialize_norm at Hout
        ihave Htail := BI.and_elim_r $$ Hcont
        ihave Hreject := BI.and_elim_l $$ Htail
        ihave Hreject := Hreject $$ %word0 %word1 %word2 %word3 %below'
          %cursorD %frontierD %historyD
        iapply Hreject $$ %hnotAccept Hruntime Hsp Hbelow Hout Hbytes Hdata
          Hbump Hstreams %hword0
      · iintro %remaining' Hstreams
        ihave Htail := BI.and_elim_r $$ Hcont
        ihave Hoom := BI.and_elim_r $$ Htail
        ihave Hoom := Hoom $$ %remaining'
        iapply Hoom $$ Hstreams

end Project.RustHashMap.Func7Proof
