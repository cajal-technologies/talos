import Project.RustHashMap.DecoderHeaderRead
import Project.RustHashMap.Func41Proof
import Project.RustHashMap.Func55Proof

/-!
# The borsh decoder: the pair buffer

A declared pair count that is not zero takes the decoder to
`Project.RustHashMap.Decoder.allocPair`, WAT lines 577 to 610.  The
fragment does three things:

1. It caps the count at 512 and asks the bump allocator for
   `8 * capacity` bytes with alignment 4.
2. It writes the three words of the vector into the frame: the capacity
   at offset 4, the pointer at offset 8, and the length 0 at offset 12.
3. It sets local 4 to `frame + 52`, the tail of the `io::Error` slot, and
   local 9 to 4, the byte offset of the first value.

The null arm at `.br_if 0` is dead.  `LiveBlock_ptr_ne_zero` reads the
non-null fact out of the block that the allocator returns.

The allocator can run out of memory, so the lemma takes the same pair of
continuations that every allocating body takes: one normal continuation
and one for the `talos.oom` trap.
-/

namespace Project.RustHashMap.Decoder

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-- The capacity of the pair buffer.  The body caps the declared count at
512 pairs. -/
def pairCapacity (count : UInt32) : UInt32 :=
  if count < 512 then count else 512

/-- The size of the pair buffer in bytes.  One pair is eight bytes. -/
def pairSize (count : UInt32) : UInt32 :=
  UInt32.ofNat (8 * (pairCapacity count).toNat)

/-- The layout that the body asks the allocator for. -/
def pairLayout (count : UInt32) : AllocLayout :=
  ⟨8 * (pairCapacity count).toNat, 4⟩

theorem pairCapacity_le (count : UInt32) : (pairCapacity count).toNat ≤ 512 := by
  unfold pairCapacity
  by_cases h : count < 512
  · rw [if_pos h]
    have hn := UInt32.lt_iff_toNat_lt.mp h
    have h512 : (512 : UInt32).toNat = 512 := by decide
    omega
  · rw [if_neg h]
    decide

theorem pairCapacity_pos (count : UInt32) (hcount : count ≠ 0) :
    0 < (pairCapacity count).toNat := by
  have hnz : count.toNat ≠ 0 := by
    intro h
    exact hcount (UInt32.toNat_inj.mp (by rw [h]; rfl))
  unfold pairCapacity
  by_cases h : count < 512
  · rw [if_pos h]; omega
  · rw [if_neg h]; decide

theorem pairSize_toNat (count : UInt32) :
    (pairSize count).toNat = 8 * (pairCapacity count).toNat := by
  unfold pairSize
  have hle := pairCapacity_le count
  exact UInt32.toNat_ofNat_of_lt' (by
    have : UInt32.size = 4294967296 := rfl
    omega)

theorem pairLayout_matches (count : UInt32) :
    (pairLayout count).Matches (pairSize count) 4 := by
  refine ⟨pairSize_toNat count, ?_⟩
  simp only [pairLayout]
  rfl

theorem pairLayout_valid (count : UInt32) (hcount : count ≠ 0) :
    (pairLayout count).Valid := by
  have hle := pairCapacity_le count
  have hpos := pairCapacity_pos count hcount
  have hsz : UInt32.size = 4294967296 := rfl
  refine ⟨?_, ?_, ⟨2, ?_⟩, ?_, ?_, ?_, ?_⟩
  · simp only [pairLayout]; omega
  · simp only [pairLayout]; omega
  · simp only [pairLayout]; norm_num
  · simp only [pairLayout]; omega
  · simp only [pairLayout]; omega
  · simp only [pairLayout]; omega
  · simp only [pairLayout]; omega

/-- The shift by three is the multiplication by eight. -/
theorem pairShift (count : UInt32) :
    pairCapacity count <<< ((3 : UInt32) % 32) = pairSize count := by
  have hle := pairCapacity_le count
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft,
    show ((3 : UInt32) % 32).toNat % 32 = 3 by decide,
    Nat.shiftLeft_eq,
    Nat.mod_eq_of_lt (by
      have : UInt32.size = 4294967296 := rfl
      have h2 : (2 : Nat) ^ 3 = 8 := by norm_num
      omega),
    pairSize_toNat]
  have h2 : (2 : Nat) ^ 3 = 8 := by norm_num
  omega

/-- The scratch error slot sits four bytes above `frame + 48`. -/
private theorem frame_plus_52 (frame : UInt32) :
    (4 : UInt32) + (48 + frame) = frame + 52 := by
  have h : (4 : UInt32) + 48 = 52 := by decide
  calc (4 : UInt32) + (48 + frame) = (4 + 48) + frame := by ac_rfl
    _ = 52 + frame := by rw [h]
    _ = frame + 52 := UInt32.add_comm _ _

set_option maxHeartbeats 2000000 in
/-- The allocation of the pair buffer. -/
theorem twp_alloc_pair [WasmSmallStepGS hlc Universal.State]
    (out hdr frame count word4 word8 word12 : UInt32)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    (l3 l4 l5 l6 l8 l9 l10 l11 l12 : Value)
    {stack : List Value} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp}
    (hcount : count ≠ 0)
    (hframeNowrap : frame.toNat + 64 < UInt32.size) :
    iprop(
      RuntimeContext ∗
      pointsTo_u32 0 (frame + 4) word4 ∗
      pointsTo_u32 0 (frame + 8) word8 ∗
      pointsTo_u32 0 (frame + 12) word12 ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ base : UInt32, ∀ finish : UInt32, ∀ allocBytes : List UInt8,
          RuntimeContext -∗
          BumpHeap heapId finish finish.toNat
            (history.allocate base (pairLayout count)) -∗
          LiveBlock heapId history.nextId base (pairLayout count) allocBytes -∗
          Streams input output raised -∗
          pointsTo_u32 0 (frame + 4) (pairCapacity count) -∗
          pointsTo_u32 0 (frame + 8) base -∗
          pointsTo_u32 0 (frame + 12) 0 -∗
          ⌜classifyBump frontier (pairLayout count) = .success base finish ∧
            base ≠ 0⌝ -∗
          WP (.running
              ⟨⟨[.i32 out, .i32 hdr],
                  [.i32 frame, .i32 0, .i32 (frame + 52), l5, l6,
                    .i32 count, .i32 base, .i32 4, l10, l11, l12],
                stack⟩,
                code, arity, remainder, controls, calls⟩
              : Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining : List UInt8,
          Streams remaining output true -∗
          Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (.running
          ⟨⟨[.i32 out, .i32 hdr],
              [.i32 frame, l3, l4, l5, l6, .i32 count, l8, l9, l10, l11, l12],
            stack⟩,
            allocPair ++ code, arity, remainder, controls, calls⟩
          : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hword4, Hword8, Hword12, Hbump, Hstreams, Hcont⟩
  obtain ⟨hf4, hf4a, hf4b, hf4c⟩ := offset_facts frame 4 4 rfl (by omega)
  obtain ⟨hf8, hf8a, hf8b, hf8c⟩ := offset_facts frame 8 8 rfl (by omega)
  obtain ⟨hf12, hf12a, hf12b, hf12c⟩ := offset_facts frame 12 12 rfl (by omega)
  have hsel : (Value.i32 (pairCapacity count)) =
      if (if count < 512 then (1 : UInt32) else 0) ≠ 0 then Value.i32 count
        else Value.i32 512 := by
    unfold pairCapacity
    by_cases hlt : count < 512
    · simp [hlt]
    · simp [hlt]
  simp only [allocPair, List.cons_append, List.nil_append]
  wasm_twp_pures [twp_localGet twp_const twp_localGet twp_const]
  iapply twp_ltU (result := if count < 512 then (1 : UInt32) else 0) rfl
  iapply twp_select (selected := Value.i32 (pairCapacity count)) hsel
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const twp_shl]
  rw [pairShift]
  wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  wasm_twp_pures [twp_const]
  have Halloc : Func55Spec (hlc := hlc) :=
    Project.RustHashMap.Func55Proof.func55_correct
  unfold Func55Spec CallContract callExpr at Halloc
  simp only [List.cons_append, List.nil_append] at Halloc
  iapply Halloc (size := pairSize count) (alignment := 4)
    (layout := pairLayout count) (heapId := heapId)
    (storedCursor := storedCursor) (frontier := frontier)
    (history := history) (input := input) (output := output)
    (raised := raised)
    (callerLocals :=
      { params := [.i32 out, .i32 hdr]
        locals := [.i32 frame, .i32 (pairSize count),
          .i32 (pairCapacity count), l5, l6, .i32 count, l8, l9, l10, l11,
          l12]
        values := [] })
    (stack := stack)
  isplitl_exact Hruntime
  isplitl_exacts [Hbump Hstreams]
  isplitl_pureexact ⟨pairLayout_matches count, pairLayout_valid count hcount,
    Or.inr rfl⟩
  unfold AllocContinuation
  cases hdecision : classifyBump frontier (pairLayout count) with
  | oom =>
      iintro Hbump Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %input
      iapply Hoom $$ Hstreams
  | success base finish =>
      isplit
      · iintro %allocBytes Hruntime Hbump Hblock Hstreams
        isimp only [ResumeWP, resumeExpr, List.nil_append]
        simp only [List.cons_append, List.nil_append]
        ihave ⟨Hblock, %hbaseNonzero⟩ :=
          Project.RustHashMap.Func41Proof.LiveBlock_ptr_ne_zero heapId
            history.nextId base (pairLayout count) allocBytes $$ Hblock
        wasm_twp_localTee [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        iapply twp_eqz (result := 0) (by simp [hbaseNonzero])
        wasm_twp_pures [twp_brIfZero twp_const]
        wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        wasm_twp_pures [twp_localGet twp_const]
        wasm_twp_rebind twp_store32 (address := frame) (offset := 12) word12
          hf12 hf12a hf12b hf12c with Hword12
        wasm_twp_pures [twp_localGet twp_localGet]
        wasm_twp_rebind twp_store32 (address := frame) (offset := 8) word8
          hf8 hf8a hf8b hf8c with Hword8
        wasm_twp_pures [twp_localGet twp_localGet]
        wasm_twp_rebind twp_store32 (address := frame) (offset := 4) word4
          hf4 hf4a hf4b hf4c with Hword4
        wasm_twp_pures [twp_localGet twp_const twp_add twp_const twp_add]
        rw [frame_plus_52]
        wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        wasm_twp_pures [twp_const]
        wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
          Nat.reduceSub, List.set]
        ihave Hnormal := BI.and_elim_l $$ Hcont
        ihave Hnormal := Hnormal $$ %base %finish %allocBytes
        iapply Hnormal $$ Hruntime Hbump Hblock Hstreams Hword4 Hword8
          Hword12 %⟨rfl, hbaseNonzero⟩
      · iintro Hbump Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        ihave Hoom := Hoom $$ %input
        iapply Hoom $$ Hstreams

end Project.RustHashMap.Decoder
