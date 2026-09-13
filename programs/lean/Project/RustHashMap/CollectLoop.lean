import Project.RustHashMap.Func15Proof
import CodeLib.RustStd.HashMap.CollectFold

/-!
# The insert loop of `collect_entries`

Absolute `func 5` reserves room for every pair and then runs one `call 18`
per pair.  This module proves the loop at WAT 923 to 940 against
`Func15Spec`, which `Project.RustHashMap.Func15Proof` discharges.
-/

namespace Project.RustHashMap.CollectLoop

open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.RustHashMap.Contracts
open Project.RustHashMap.Allocator
open Project.RustHashMap.AllocatorContracts
open Project.RustHashMap.EntryContracts
open Project.RustHashMap.BodyContracts
open Project.RustHashMap.CollectContract
open Project.RustHashMap.CollectBodyContracts
open Project.RustHashMap.FrameCells
open scoped Wasm.SmallStep.Outcome

/-! ## The pair buffer as a word array -/

/-- The pair buffer read as words: each entry gives its key and then its
value.  The compiled loop loads the key at `cur` and the value at `cur + 4`,
so word `2 i` is the key of entry `i` and word `2 i + 1` is its value. -/
def pairWords (entries : List (UInt32 × UInt32)) : List UInt32 :=
  entries.flatMap (fun entry => [entry.1, entry.2])

@[simp] theorem pairWords_nil : pairWords [] = [] := rfl

theorem pairWords_cons (entry : UInt32 × UInt32)
    (entries : List (UInt32 × UInt32)) :
    pairWords (entry :: entries) = entry.1 :: entry.2 :: pairWords entries :=
  rfl

theorem pairWords_append (xs ys : List (UInt32 × UInt32)) :
    pairWords (xs ++ ys) = pairWords xs ++ pairWords ys :=
  List.flatMap_append

@[simp] theorem pairWords_length (entries : List (UInt32 × UInt32)) :
    (pairWords entries).length = 2 * entries.length := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rw [pairWords_cons, List.length_cons, List.length_cons, ih,
      List.length_cons]
    omega

/-- The wire bytes of the entry list are the byte serialization of its
words.  `entryCodec` lays the key down first, which is what `pairWords`
repeats. -/
theorem serialize_eq_pairWords (entries : List (UInt32 × UInt32)) :
    entryCodec.serialize entries =
      WordCodec.u32le.serialize (pairWords entries) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
    rw [WordCodec.serialize_cons, ih, pairWords_cons,
      WordCodec.serialize_cons, WordCodec.serialize_cons,
      ← List.append_assoc]
    rfl

private theorem pairWords_drop (entries : List (UInt32 × UInt32)) (k : Nat)
    (hk : k < entries.length) :
    pairWords (entries.drop k) =
      (entries[k]).1 :: (entries[k]).2 :: pairWords (entries.drop (k + 1)) := by
  rw [List.drop_eq_getElem_cons hk, pairWords_cons]

/-- Word `2 k` of the buffer is the key of entry `k`. -/
theorem pairWords_getElem_key (entries : List (UInt32 × UInt32)) (k : Nat)
    (hk : k < entries.length)
    (hbound : 2 * k < (pairWords entries).length) :
    (pairWords entries)[2 * k] = (entries[k]).1 := by
  have hsplit : pairWords entries =
      pairWords (entries.take k) ++ pairWords (entries.drop k) := by
    rw [← pairWords_append, List.take_append_drop]
  have hlen : (pairWords (entries.take k)).length = 2 * k := by
    rw [pairWords_length, List.length_take]
    omega
  rw [List.getElem_of_eq hsplit hbound,
    List.getElem_append_right (by omega)]
  simp only [hlen, Nat.sub_self, pairWords_drop entries k hk,
    List.getElem_cons_zero]

/-- Word `2 k + 1` of the buffer is the value of entry `k`. -/
theorem pairWords_getElem_value (entries : List (UInt32 × UInt32)) (k : Nat)
    (hk : k < entries.length)
    (hbound : 2 * k + 1 < (pairWords entries).length) :
    (pairWords entries)[2 * k + 1] = (entries[k]).2 := by
  have hsplit : pairWords entries =
      pairWords (entries.take k) ++ pairWords (entries.drop k) := by
    rw [← pairWords_append, List.take_append_drop]
  have hlen : (pairWords (entries.take k)).length = 2 * k := by
    rw [pairWords_length, List.length_take]
    omega
  rw [List.getElem_of_eq hsplit hbound,
    List.getElem_append_right (by omega)]
  simp only [hlen, Nat.add_sub_cancel_left, pairWords_drop entries k hk,
    List.getElem_cons_succ, List.getElem_cons_zero]

/-! ## The shape of the loop -/

section Machine

variable [WasmSmallStepGS hlc Universal.State]

/-- The locals at the head of the insert loop.  Local 0 is the map output
slot and local 1 the capacity that the body frees at WAT 952.  Local 2 is
the frame, local 3 the running pointer, local 4 the buffer start, local 5
the seed counter and local 6 the end of the buffer. -/
@[reducible] def collectLocals (mapSlot cap frame cur ptr endAddr : UInt32)
    (seed : UInt64) : Locals :=
  { params := [.i32 mapSlot, .i32 cap],
    locals := [.i32 frame, .i32 cur, .i32 ptr, .i64 seed, .i32 endAddr],
    values := [] }

/-- WAT 923 to 940: one insert, the pointer advance and the back edge. -/
def insertLoopBody : Program :=
  [.localGet 2, .localGet 2, .const 16, .add, .localGet 3, .load32 0,
    .localGet 3, .const 4, .add, .load32 0, .call 18,
    .localGet 3, .const 8, .add, .localTee 3, .localGet 6, .ne, .br_if 0]

/-- WAT 899 to 941: the block that reserves room for every pair and then
runs the insert loop.  The guard at the head skips the whole block when the
entry count is zero. -/
def insertBlockBody : Program :=
  [.localGet 3, .eqz, .br_if 0, .localGet 4, .localGet 3, .const 3, .shl,
    .add, .localSet 6, .localGet 2, .const 8, .add, .localGet 2, .const 16,
    .add, .localGet 3, .localGet 2, .const 32, .add, .const 1, .call 17,
    .localGet 4, .localSet 3, .loop 0 0 insertLoopBody]

/-- The insert block is instruction 37 of the compiled body, and the loop
body inside it is the one this module steps through. -/
theorem func2_insert_block :
    Project.RustHashMap.func2 =
      Project.RustHashMap.func2.take 37 ++
        .block 0 0 insertBlockBody :: Project.RustHashMap.func2.drop 38 := by
  rfl

/-- The eight-byte out slot of `call 18`.  The loop drops every result, so
the bytes carry no meaning between iterations. -/
def OutSlot (addr : UInt32) : HeapIProp :=
  iprop(∃ bytes : List UInt8, ⌜bytes.length = 8⌝ ∗ Slices.ByteSlice 0 addr bytes)

/-- The stack that `func 18` writes below the frame of `func 5`. -/
def BelowFrame (frame : UInt32) : HeapIProp :=
  iprop(∃ bytes : List UInt8, StackBelow frame insertDepth bytes)

/-- What the loop hands to the code after it: every pair is in the table. -/
def InsertLoopExit (mapSlot cap frame ptr : UInt32) (seed : UInt64)
    (k0 k1 : UInt64) (entries : List (UInt32 × UInt32))
    (t0 : HashMap.Table UInt32 UInt32)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) : HeapIProp :=
  iprop(RuntimeContext -∗ StackPointer frame -∗ BelowFrame frame -∗
    OutSlot frame -∗
    HashMap.Table.HashMapAt 0 (frame + 16) k0 k1
      (HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0 entries) -∗
    Slices.WordSlice 0 ptr (pairWords entries) -∗
    WP (Expr.running
        ⟨collectLocals mapSlot cap frame
            (ptr + UInt32.ofNat (8 * entries.length)) ptr
            (ptr + UInt32.ofNat (8 * entries.length)) seed,
          contCode, arity, remainder, controls, calls⟩ :
          Expr Universal.State) @ s; E [{ Φ }])

/-- Four times a word offset is the byte offset. -/
private theorem four_mul_ofNat (n : Nat) :
    (4 : UInt32) * UInt32.ofNat n = UInt32.ofNat (4 * n) := by
  rw [UInt32.ofNat_mul 4 n]
  rfl

/-- Two anonymous words at the bottom of the frame are an out slot again. -/
private theorem outSlot_of_words (addr tag payload : UInt32)
    (hnowrap : addr.toNat + 8 < UInt32.size) :
    iprop(pointsTo_u32 (α := Universal.State) 0 addr tag ∗
      pointsTo_u32 0 (addr + 4) payload) ⊢ OutSlot addr := by
  iintro ⟨Htag, Hpayload⟩
  ihave Harray : arrayAt 0 addr [tag, payload] $$ [Htag Hpayload]
  · isimp only [arrayAt]
    iframe Htag Hpayload
  ihave Hbytes := (Slices.arrayAt_eq_wordCells 0 addr [tag, payload]).mp $$ Harray
  isimp only [OutSlot]
  iexists (WordCodec.u32le.serialize [tag, payload])
  isplitl_pureexact (by simp)
  · isimp only [Slices.ByteSlice]
    isplitl_pureexact (by simpa using hnowrap)
    · iexact Hbytes

/-- The loop drops the result of every insert, so the out slot comes back
as eight anonymous bytes. -/
private theorem outSlot_of_option (addr : UInt32) (o : Option UInt32)
    (hnowrap : addr.toNat + 8 < UInt32.size) :
    HashMap.Table.optionU32At (α := Universal.State) 0 addr o ⊢ OutSlot addr := by
  iintro Hoption
  ihave ⟨%tag, %payload, Htag, Hpayload⟩ :=
    HashMap.Table.optionU32At_forget 0 addr o $$ Hoption
  iapply outSlot_of_words addr tag payload hnowrap
  iframe Htag Hpayload

/-- The measure of the loop: the pairs that are not in the table yet. -/
private def loopMeasure (entries : List (UInt32 × UInt32)) (k : Nat) : Nat :=
  entries.length - k

/-- The invariant at the head of iteration `k`: the first `k` pairs are in
the table, and the running pointer is `ptr + 8 k`. -/
private def LoopInv (mapSlot cap frame ptr : UInt32) (seed : UInt64)
    (k0 k1 : UInt64) (entries : List (UInt32 × UInt32))
    (t0 : HashMap.Table UInt32 UInt32)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset)
    (Φ : ObservableOutcome → HeapIProp) (k : Nat) : HeapIProp :=
  iprop(⌜k < entries.length⌝ ∗
    RuntimeContext ∗ StackPointer frame ∗ BelowFrame frame ∗
    OutSlot frame ∗
    HashMap.Table.HashMapAt 0 (frame + 16) k0 k1
      (HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0
        (entries.take k)) ∗
    Slices.WordSlice 0 ptr (pairWords entries) ∗
    InsertLoopExit mapSlot cap frame ptr seed k0 k1 entries t0 contCode arity
      remainder controls calls s E Φ)

set_option maxHeartbeats 2000000 in
/-- The insert loop of `collect_entries`, WAT 923 to 940.  One `call 18` per
pair, in wire order, and the model side is the fold of
`CodeLib.RustStd.HashMap.CollectFold`. -/
theorem twp_insert_loop
    (mapSlot cap frame ptr : UInt32) (seed k0 k1 : UInt64)
    (entries : List (UInt32 × UInt32))
    (t0 : HashMap.Table UInt32 UInt32)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hentries : 0 < entries.length)
    (hptr : ptr.toNat + 8 * entries.length < UInt32.size)
    (hdepth : insertDepth ≤ frame.toNat)
    (hframe : frame.toNat + 48 < UInt32.size)
    (hwf : HashMap.Table.WF (HashMap.SipHash.hashU32 k0 k1) t0)
    (hclean : HashMap.Table.Clean t0)
    (hgrowth : entries.length ≤ t0.growthLeft)
    (hbuckets : t0.buckets < UInt32.size) :
    iprop(
      RuntimeContext ∗ StackPointer frame ∗ BelowFrame frame ∗
      OutSlot frame ∗
      HashMap.Table.HashMapAt 0 (frame + 16) k0 k1 t0 ∗
      Slices.WordSlice 0 ptr (pairWords entries) ∗
      InsertLoopExit mapSlot cap frame ptr seed k0 k1 entries t0 contCode arity
        remainder controls calls s E Φ) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame ptr ptr
              (ptr + UInt32.ofNat (8 * entries.length)) seed,
            .loop 0 0 insertLoopBody :: contCode, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout, Hmap, Hbuf, Hcont⟩
  iapply Wasm.SmallStep.twp_loop_wf_family
    (ι := Nat)
    (measure := loopMeasure entries)
    (locals := fun k => collectLocals mapSlot cap frame
      (ptr + UInt32.ofNat (8 * k)) ptr
      (ptr + UInt32.ofNat (8 * entries.length)) seed)
    (I := LoopInv mapSlot cap frame ptr seed k0 k1 entries t0 contCode arity
      remainder controls calls s E Φ)
    (initial := 0)
    (initialLocals := collectLocals mapSlot cap frame ptr ptr
      (ptr + UInt32.ofNat (8 * entries.length)) seed)
    (by rw [show ptr + UInt32.ofNat (8 * 0) = ptr from by
      simp only [Nat.mul_zero]
      exact UInt32.add_zero ptr])
    (show ([] : List Value) = _ from rfl)
  · intro k
    iintro Hrec Hinv
    isimp only [LoopInv] at Hinv
    icases Hinv with ⟨%hk, Hruntime, Hsp, Hbelow, Hout, Hmap, Hbuf, Hcont⟩
    isimp only [BelowFrame] at Hbelow
    isimp only [OutSlot] at Hout
    icases Hbelow with ⟨%belowBytes, Hbelow⟩
    icases Hout with ⟨%outBytes, %houtLength, Hout⟩
    have hsize : UInt32.size = 4294967296 := rfl
    -- the running pointer and the two cells of pair `k`
    have hcurNat : (ptr + UInt32.ofNat (8 * k)).toNat = ptr.toNat + 8 * k :=
      Slices.byteOffset_toNat ptr (8 * k) (by omega)
    have hmulKey : (4 : UInt32) * UInt32.ofNat (2 * k) = UInt32.ofNat (8 * k) := by
      rw [four_mul_ofNat, show 4 * (2 * k) = 8 * k by omega]
    have hmulValue :
        (4 : UInt32) * UInt32.ofNat (2 * k + 1) = UInt32.ofNat (8 * k) + 4 := by
      rw [four_mul_ofNat, show 4 * (2 * k + 1) = 8 * k + 4 by omega,
        UInt32.ofNat_add]
      rfl
    have hkeyIdx : 2 * k < (pairWords entries).length := by
      rw [pairWords_length]; omega
    have hvalueIdx : 2 * k + 1 < (pairWords entries).length := by
      rw [pairWords_length]; omega
    obtain ⟨hk1, hk2, hk3⟩ := Func15Insert.addr3 (ptr + UInt32.ofNat (8 * k)) (by omega)
    have hvalueNat : (ptr + UInt32.ofNat (8 * k) + 4).toNat = ptr.toNat + 8 * k + 4 := by
      have hstep4 : (ptr + UInt32.ofNat (8 * k) + UInt32.ofNat 4).toNat =
          (ptr + UInt32.ofNat (8 * k)).toNat + 4 :=
        Slices.byteOffset_toNat (ptr + UInt32.ofNat (8 * k)) 4 (by omega)
      rw [hcurNat] at hstep4
      exact hstep4
    obtain ⟨hv1, hv2, hv3⟩ := Func15Insert.addr3 (ptr + UInt32.ofNat (8 * k) + 4) (by omega)
    -- the frame cells
    have hframe16 : (frame + 16).toNat = frame.toNat + 16 := by
      have := Slices.byteOffset_toNat frame 16 (by omega)
      simpa using this
    -- the model side
    obtain ⟨hwfk, hcleank, hbucketsk, hgrowthk⟩ :=
      HashMap.Table.insertAll_prefix (HashMap.SipHash.hashU32 k0 k1) k t0 entries
        hwf hclean hgrowth (by omega)
    have hgrowthLe := hcleank.growthLeft_le
    rw [hbucketsk] at hgrowthLe
    -- the machine
    simp only [Wasm.SmallStep.loopBodyExpr, collectLocals, insertLoopBody]
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_add]
      rewriting [UInt32.add_comm 16 frame]
    wasm_twp_pures [twp_localGet]
    have hgetKey := Slices.WordSlice_get (α := Universal.State) 0 ptr
      (pairWords entries) (2 * k) hkeyIdx
    rw [hmulKey, pairWords_getElem_key entries k hk hkeyIdx] at hgetKey
    ihave ⟨Hkey, HkeyClose⟩ := hgetKey $$ Hbuf
    wasm_twp_rebind twp_load32_addr (addr := ptr + UInt32.ofNat (8 * k))
      (entries[k]).1 hk1 hk2 hk3 with Hkey
    ihave Hbuf := HkeyClose $$ Hkey
    wasm_twp_pures [twp_localGet twp_const twp_add]
      rewriting [UInt32.add_comm 4 (ptr + UInt32.ofNat (8 * k))]
    have hgetValue := Slices.WordSlice_get (α := Universal.State) 0 ptr
      (pairWords entries) (2 * k + 1) hvalueIdx
    rw [hmulValue, ← UInt32.add_assoc,
      pairWords_getElem_value entries k hk hvalueIdx] at hgetValue
    ihave ⟨Hvalue, HvalueClose⟩ := hgetValue $$ Hbuf
    wasm_twp_rebind twp_load32_addr (addr := ptr + UInt32.ofNat (8 * k) + 4)
      (entries[k]).2 hv1 hv2 hv3 with Hvalue
    ihave Hbuf := HvalueClose $$ Hvalue
    -- `call 18`
    have Hins : Func15Spec (hlc := hlc) :=
      Project.RustHashMap.Func15Proof.func15_correct
    unfold Func15Spec CallContract callExpr at Hins
    simp only [List.cons_append, List.nil_append] at Hins
    iapply Hins (sp := frame) (out := frame) (mapBase := frame + 16)
      (key := (entries[k]).1) (value := (entries[k]).2) (k0 := k0) (k1 := k1)
      (t := HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0
        (entries.take k))
      (outBefore := outBytes) (below := belowBytes)
      (callerLocals := collectLocals mapSlot cap frame
        (ptr + UInt32.ofNat (8 * k)) ptr
        (ptr + UInt32.ofNat (8 * entries.length)) seed)
      (stack := [])
    isplitl_exacts [Hruntime Hsp Hbelow Hout Hmap]
    isplitl_pureexact ⟨houtLength, hdepth, by omega, by omega, hwfk, hcleank,
      by omega, by omega⟩
    iintro %below' Hruntime Hsp Hbelow Hoption Hmap
    isimp only [ResumeWP, resumeExpr, List.nil_append]
    ihave Hout := outSlot_of_option frame _ (by omega) $$ Hoption
    -- the pointer advance
    wasm_twp_pures [twp_localGet twp_const twp_add]
      rewriting [UInt32.add_comm 8 (ptr + UInt32.ofNat (8 * k))]
    have hstep : ptr + UInt32.ofNat (8 * k) + 8 = ptr + UInt32.ofNat (8 * (k + 1)) := by
      rw [show 8 * (k + 1) = 8 * k + 8 by omega, UInt32.ofNat_add, ← UInt32.add_assoc]
      rfl
    rw [hstep]
    wasm_twp_localTee [List.set, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceSub]
    wasm_twp_pures [twp_localGet]
    have hnextNat : (ptr + UInt32.ofNat (8 * (k + 1))).toNat = ptr.toNat + 8 * (k + 1) :=
      Slices.byteOffset_toNat ptr (8 * (k + 1)) (by omega)
    have hendNat : (ptr + UInt32.ofNat (8 * entries.length)).toNat =
        ptr.toNat + 8 * entries.length :=
      Slices.byteOffset_toNat ptr (8 * entries.length) (by omega)
    -- the model fact that the tail of both branches uses
    have hstepModel :
        HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0
            (entries.take (k + 1)) =
          (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
            (HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0
              (entries.take k)) (entries[k]).1 (entries[k]).2).2 := by
      rw [show entries.take (k + 1) = entries.take k ++ [entries[k]] by
        rw [List.take_add_one, List.getElem?_eq_getElem hk]; rfl,
        HashMap.Table.insertAll_append, HashMap.Table.insertAll_cons,
        HashMap.Table.insertAll_nil]
    by_cases hlast : k + 1 = entries.length
    · -- the last pair: fall out of the loop
      have hsame : ptr + UInt32.ofNat (8 * (k + 1)) =
          ptr + UInt32.ofNat (8 * entries.length) := by rw [hlast]
      iapply twp_ne (result := 0) (by rw [if_neg (not_not_intro hsame)])
      iapply twp_brIfZero
      wasm_twp_pures [twp_exitControl]
      simp only [List.take_zero, List.nil_append]
      have hfinal :
          HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0 entries =
            (HashMap.Table.insert (HashMap.SipHash.hashU32 k0 k1)
              (HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0
                (entries.take k)) (entries[k]).1 (entries[k]).2).2 := by
        rw [← hstepModel, hlast, List.take_length]
      ihave HbelowFrame : BelowFrame frame $$ [Hbelow]
      · isimp only [BelowFrame]
        iexists below'
        iexact Hbelow
      ihave HmapAll : HashMap.Table.HashMapAt 0 (frame + 16) k0 k1
          (HashMap.Table.insertAll (HashMap.SipHash.hashU32 k0 k1) t0 entries)
        $$ [Hmap]
      · rw [hfinal]
        iexact Hmap
      isimp only [InsertLoopExit] at Hcont
      ihave Hexit := Hcont $$ Hruntime Hsp HbelowFrame Hout HmapAll Hbuf
      rw [hsame]
      iexact Hexit
    · -- one more pair: take the back edge
      have hne : ptr + UInt32.ofNat (8 * (k + 1)) ≠
          ptr + UInt32.ofNat (8 * entries.length) := by
        intro heq
        have := congrArg UInt32.toNat heq
        rw [hnextNat, hendNat] at this
        omega
      iapply twp_ne (result := 1) (by rw [if_pos hne])
      iapply twp_brIf (by decide) (by rfl)
      simp only [List.take_zero, List.nil_append]
      ihave Hback := Hrec $$ %(k + 1)
        %(by simp only [loopMeasure]; omega : loopMeasure entries (k + 1) <
          loopMeasure entries k)
      iapply Hback
      isimp only [LoopInv]
      isplitl_pureexact (by omega : k + 1 < entries.length)
      iframe Hruntime Hsp
      isplitl [Hbelow]
      · isimp only [BelowFrame]
        iexists below'
        iexact Hbelow
      isplitl [Hout]
      · iexact Hout
      isplitl [Hmap]
      · rw [hstepModel]
        iexact Hmap
      iframe Hbuf Hcont
  · isimp only [LoopInv]
    isplitl_pureexact hentries
    iframe Hruntime Hsp Hbelow Hout
    isplitl [Hmap]
    · isimp only [List.take_zero, HashMap.Table.insertAll_nil]
      iexact Hmap
    · iframe Hbuf Hcont


end Machine

end Project.RustHashMap.CollectLoop
