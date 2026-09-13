import Project.RustHashMap.CollectPrologue

/-!
# The reserve block of `collect_entries`

Absolute `func 5` reserves room for every pair and then inserts them.
`Project.RustHashMap.CollectPrologue` covers the code before the reserve, and
`Project.RustHashMap.CollectLoop` covers the insert loop inside it.  This
module joins the two.  `twp_insert_block` is the rule for instruction 37 of
the compiled body, WAT 898 to 941.

The block has two paths.  An empty entry list skips it, and the table stays
the static empty singleton, which is `Table.ofEntries` of the empty list.
Otherwise the rule reads the end of the pair buffer as `ptr + 8 * length`,
calls absolute `func 17` once with the exact count, and hands the returned
`Table.withCapacity` to `CollectLoop.twp_insert_loop`.
`CollectFold.ofEntries_eq_insertAll` names the two phases together, so both
paths end at `Table.ofEntries`.

Two premises are open work, and each one is an argument here rather than a
fact the rule proves.

* `Func14Spec`, the contract of absolute `func 17`, is a hypothesis.  The
  body of that function needs an allocator call at alignment 8, which
  `Func55Spec` does not cover yet.
* `Table.TableAt 0 (frame + 16) Table.empty` is a resource.  The compiled
  body copies the static singleton out of the data segment, and
  `Table.SingletonBody` asks for nine control bytes while the segment holds
  eight, so no caller can build it today.
-/

namespace Project.RustHashMap.CollectReserve

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
open Project.RustHashMap.CollectLoop
open Project.RustHashMap.CollectPrologue
open scoped Wasm.SmallStep.Outcome

/-! ## Arithmetic of the pair buffer -/

/-- The shift by three is the multiplication by eight. -/
private theorem shift_three (len : UInt32) (hbound : 8 * len.toNat < UInt32.size) :
    len <<< (3 : UInt32) = UInt32.ofNat (8 * len.toNat) := by
  have hsz : UInt32.size = 4294967296 := rfl
  have h2 : (2 : Nat) ^ 3 = 8 := by norm_num
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
  have hlt : len.toNat * 8 < 2 ^ 32 := by omega
  apply UInt32.toNat_inj.mp
  rw [UInt32.toNat_shiftLeft, show (3 : UInt32).toNat % 32 = 3 by decide,
    Nat.shiftLeft_eq, h2, Nat.mod_eq_of_lt hlt,
    UInt32.toNat_ofNat_of_lt' hbound]
  omega

/-- A table of the exact entry count is the model that `collect_entries`
builds: one `with_capacity` and then the insert fold. -/
private theorem insertAll_withCapacity (hash : UInt32 → UInt64)
    (entries : List (UInt32 × UInt32)) :
    HashMap.Table.insertAll hash
        (HashMap.Table.withCapacity entries.length) entries
      = HashMap.Table.ofEntries hash entries :=
  (HashMap.Table.ofEntries_eq_insertAll hash entries).symm

/-- The empty entry list gives the static empty table back. -/
private theorem ofEntries_nil (hash : UInt32 → UInt64) :
    HashMap.Table.ofEntries hash ([] : List (UInt32 × UInt32))
      = HashMap.Table.empty := by
  rw [HashMap.Table.ofEntries_eq_insertAll, List.length_nil,
    HashMap.Table.insertAll_nil, HashMap.Table.withCapacity, if_pos rfl]

/-! ## The shape of the block -/

/-- The reserve block is instruction 37 of the compiled body. -/
theorem func2_reserve_block :
    Project.RustHashMap.func2.drop 37
      = .block 0 0 insertBlockBody :: Project.RustHashMap.func2.drop 38 := by
  rfl

section Machine

variable [WasmSmallStepGS hlc Universal.State]

set_option maxHeartbeats 2000000 in
/-- WAT 898 to 941.  The block skips itself when the entry count is zero.
Otherwise it computes the end of the pair buffer, calls absolute `func 17`
once with the exact count, and runs the insert loop. -/
theorem twp_insert_block
    (hreserve : Func14Spec (hlc := hlc))
    (mapSlot cap frame ptr endAddr0 len : UInt32) (seed k0 k1 : UInt64)
    (entries : List (UInt32 × UInt32)) (lower : List UInt8)
    (heapId : GName) (storedCursor : UInt32) (frontier : Nat)
    (history : AllocationHistory) (input output : List UInt8) (raised : Bool)
    (contCode : Program) (arity : Nat) (remainder : List Value)
    (controls : List ControlFrame) (calls : List CallFrame)
    (s : Stuckness) (E : CoPset) (Φ : ObservableOutcome → HeapIProp)
    (hlen : entries.length = len.toNat)
    (hcap : len.toNat ≤ maxTableCapacity)
    (hptr : ptr.toNat + 8 * entries.length < UInt32.size)
    (hdepth : collectBelowDepth ≤ frame.toNat)
    (hframe : frame.toNat + 48 < UInt32.size) :
    iprop(RuntimeContext ∗
      StackPointer frame ∗
      StackBelow frame collectBelowDepth lower ∗
      OutSlot frame ∗
      OutSlot (frame + 8) ∗
      HashMap.Table.TableAt 0 (frame + 16) HashMap.Table.empty ∗
      pointsTo_u64 0 (frame + 32) k0 ∗
      pointsTo_u64 0 (frame + 40) k1 ∗
      Slices.WordSlice 0 ptr (pairWords entries) ∗
      BumpHeap heapId storedCursor frontier history ∗
      Streams input output raised ∗
      ((∀ cur' : UInt32, ∀ endAddr' : UInt32, ∀ lower' : List UInt8,
          ∀ storedCursor' : UInt32, ∀ frontier' : Nat,
          ∀ history' : AllocationHistory,
          RuntimeContext -∗
          StackPointer frame -∗
          StackBelow frame collectBelowDepth lower' -∗
          OutSlot frame -∗
          OutSlot (frame + 8) -∗
          HashMap.Table.HashMapAt 0 (frame + 16) k0 k1
            (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries) -∗
          Slices.WordSlice 0 ptr (pairWords entries) -∗
          BumpHeap heapId storedCursor' frontier' history' -∗
          Streams input output raised -∗
          WP (Expr.running
              ⟨collectLocals mapSlot cap frame cur' ptr endAddr' seed,
                contCode, arity, remainder, controls, calls⟩ :
              Expr Universal.State) @ s; E [{ Φ }]) ∧
        (∀ remaining' : List UInt8,
          Streams remaining' output true -∗
            Φ (.trapped (.host OOM.trapMessage))))) ⊢
      WP (Expr.running
          ⟨collectLocals mapSlot cap frame len ptr endAddr0 seed,
            .block 0 0 insertBlockBody :: contCode, arity, remainder,
            controls, calls⟩ : Expr Universal.State) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hsp, Hbelow, Hout0, Hout8, Htable, Hk0, Hk1, Hbuf,
    Hbump, Hstreams, Hcont⟩
  have hmax : maxTableCapacity = 117440512 := rfl
  have hcbd : collectBelowDepth = 144 := rfl
  have hrd : resizeDepth = 128 := rfl
  have hid : insertDepth = 144 := rfl
  have hsize : UInt32.size = 4294967296 := rfl
  have a32 : frame + 16 + 16 = frame + 32 := by rw [UInt32.add_assoc]; rfl
  have a40 : frame + 16 + 24 = frame + 40 := by rw [UInt32.add_assoc]; rfl
  have a48 : frame + 32 + 8 = frame + 40 := by rw [UInt32.add_assoc]; rfl
  have e8 : (frame + 8).toNat = frame.toNat + 8 := by
    simpa using Slices.byteOffset_toNat frame 8 (by omega)
  have e16 : (frame + 16).toNat = frame.toNat + 16 := by
    simpa using Slices.byteOffset_toNat frame 16 (by omega)
  have e32 : (frame + 32).toNat = frame.toNat + 32 := by
    simpa using Slices.byteOffset_toNat frame 32 (by omega)
  simp only [insertBlockBody, collectLocals]
  iapply Wasm.SmallStep.twp_block
  simp only [List.drop_nil]
  wasm_twp_pures [twp_localGet]
  by_cases hzero : len = 0
  · -- no pair: the block skips itself
    have hnil : entries = [] := by
      have : entries.length = 0 := by rw [hlen, hzero, UInt32.toNat_zero]
      exact List.eq_nil_of_length_eq_zero this
    iapply twp_eqz (result := 1) (by rw [if_pos hzero])
    iapply twp_brIf (by decide) (by rfl)
    simp only [List.take_zero, List.nil_append]
    ihave Hmap : HashMap.Table.HashMapAt 0 (frame + 16) k0 k1
        (HashMap.Table.ofEntries (HashMap.SipHash.hashU32 k0 k1) entries) $$
        [Htable Hk0 Hk1]
    · isimp only [HashMap.Table.HashMapAt, a32, a40, hnil, ofEntries_nil]
      iframe Htable Hk0 Hk1
    ihave Hnormal := BI.and_elim_l $$ Hcont
    ihave Hexit := Hnormal $$ %len %endAddr0 %lower %storedCursor %frontier
      %history Hruntime Hsp Hbelow Hout0 Hout8 Hmap Hbuf Hbump Hstreams
    iexact Hexit
  · -- at least one pair
    have hpos : 0 < len.toNat := by
      rcases Nat.eq_zero_or_pos len.toNat with h | h
      · exact absurd (UInt32.toNat_inj.mp (by rw [UInt32.toNat_zero]; exact h))
          hzero
      · exact h
    have hentries : 0 < entries.length := by omega
    have hshift : len <<< ((3 : UInt32) % 32) + ptr
        = ptr + UInt32.ofNat (8 * entries.length) := by
      rw [show ((3 : UInt32) % 32) = 3 from rfl,
        shift_three len (by omega), hlen, UInt32.add_comm]
    have hc31 : entries.length * 8 / 7 ≤ 2 ^ 31 := by
      have h1 : entries.length * 8 ≤ 939524096 := by omega
      have h2 := Nat.div_le_div_right (c := 7) h1
      have h3 : (939524096 : Nat) / 7 = 134217728 := by norm_num
      have h4 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
      omega
    have hc32 : entries.length * 8 / 7 ≤ 2 ^ 32 := by
      have h4 : (2 : Nat) ^ 31 = 2147483648 := by norm_num
      have h5 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
      omega
    iapply twp_eqz (result := 0) (by rw [if_neg hzero])
    iapply twp_brIfZero
    wasm_twp_pures [twp_localGet twp_localGet twp_const twp_shl twp_add]
      rewriting [hshift]
    wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
      Nat.reduceSub, List.set]
    wasm_twp_pures [twp_localGet twp_const twp_add twp_localGet twp_const
      twp_add twp_localGet twp_localGet twp_const twp_add twp_const]
      rewriting [UInt32.add_comm 8 frame, UInt32.add_comm 16 frame,
        UInt32.add_comm 32 frame]
    -- the reserve
    isimp only [OutSlot] at Hout8
    icases Hout8 with ⟨%out8, %hout8, Hout8⟩
    ihave ⟨Hlow, Hown⟩ :=
      frame_split frame collectBelowDepth resizeDepth lower (by decide) $$ Hbelow
    ihave ⟨Hlow, %hlowLength⟩ :=
      StackBelow_length (frame - UInt32.ofNat resizeDepth)
        (collectBelowDepth - resizeDepth)
        (lower.take (collectBelowDepth - resizeDepth)) $$ Hlow
    isimp only [← a48] at Hk1
    unfold Func14Spec CallContract callExpr at hreserve
    simp only [List.cons_append, List.nil_append] at hreserve
    iapply hreserve (sp := frame) (out := frame + 8) (table := frame + 16)
      (additional := len) (hasher := frame + 32) (k0 := k0) (k1 := k1)
      (t := HashMap.Table.empty) (outBefore := out8)
      (below := lower.drop (collectBelowDepth - resizeDepth))
      (heapId := heapId) (storedCursor := storedCursor) (frontier := frontier)
      (history := history) (input := input) (output := output)
      (raised := raised)
      (callerLocals :=
        ⟨[.i32 mapSlot, .i32 cap],
          [.i32 frame, .i32 len, .i32 ptr, .i64 seed,
            .i32 (ptr + UInt32.ofNat (8 * entries.length))], []⟩)
      (stack := [])
    isplitl_exacts [Hruntime Hsp Hown Hout8 Htable Hk0 Hk1 Hbump Hstreams]
    isplitl_pureexact ⟨hout8, by omega, by omega, by omega, by omega, rfl,
      hpos, hcap⟩
    isplit
    · iintro %word1 %below' %storedCursor' %frontier' %history'
        Hruntime Hsp Hown Hout8 Htable Hk0 Hk1 Hbump Hstreams
      isimp only [ResumeWP, resumeExpr, List.nil_append]
      wasm_twp_pures [twp_localGet]
      wasm_twp_localSet [List.length_cons, List.length_nil, Nat.reduceAdd,
        Nat.reduceSub, List.set]
      isimp only [a48] at Hk1
      isimp only [← hlen] at Htable
      ihave Hbelow :=
        frame_join frame collectBelowDepth resizeDepth
          (lower.take (collectBelowDepth - resizeDepth)) below'
          hlowLength (by decide) $$ [Hlow Hown]
      · iframe Hlow Hown
      ihave Hbelow : BelowFrame frame $$ [Hbelow]
      · isimp only [BelowFrame]
        iexists (lower.take (collectBelowDepth - resizeDepth) ++ below')
        isimp only [show insertDepth = collectBelowDepth from rfl]
        iexact Hbelow
      ihave Hmap : HashMap.Table.HashMapAt 0 (frame + 16) k0 k1
          (HashMap.Table.withCapacity entries.length) $$ [Htable Hk0 Hk1]
      · isimp only [HashMap.Table.HashMapAt, a32, a40]
        iframe Htable Hk0 Hk1
      ihave Hout8 : OutSlot (frame + 8) $$ [Hout8]
      · isimp only [OutSlot]
        iexists (WordCodec.u32le.serialize [okTag, word1])
        isplitl_pureexact (by simp)
        · iexact Hout8
      iapply CollectLoop.twp_insert_loop
        (mapSlot := mapSlot) (cap := cap) (frame := frame) (ptr := ptr)
        (seed := seed) (k0 := k0) (k1 := k1) (entries := entries)
        (t0 := HashMap.Table.withCapacity entries.length)
        (hentries := hentries) (hptr := hptr) (hdepth := by omega)
        (hframe := hframe)
        (hwf := HashMap.Table.withCapacity_wf hc32 _)
        (hclean := HashMap.Table.withCapacity_clean _)
        (hgrowth := HashMap.Table.withCapacity_growthLeft hc32)
        (hbuckets := by
          have := HashMap.Table.withCapacity_buckets_lt
            (K := UInt32) (V := UInt32) hc31
          have h5 : (2 : Nat) ^ 32 = 4294967296 := by norm_num
          omega)
      isplitl_exacts [Hruntime Hsp Hbelow Hout0 Hmap Hbuf]
      isimp only [InsertLoopExit]
      iintro Hruntime Hsp Hbelow Hout0 Hmap Hbuf
      isimp only [insertAll_withCapacity] at Hmap
      isimp only [BelowFrame] at Hbelow
      icases Hbelow with ⟨%bytes', Hbelow⟩
      isimp only [show insertDepth = collectBelowDepth from rfl] at Hbelow
      wasm_twp_pures [twp_exitControl]
      dsimp only
      simp only [List.take_zero, List.nil_append]
      ihave Hnormal := BI.and_elim_l $$ Hcont
      ihave Hexit := Hnormal $$ %(ptr + UInt32.ofNat (8 * entries.length))
        %(ptr + UInt32.ofNat (8 * entries.length)) %bytes' %storedCursor'
        %frontier' %history'
        Hruntime Hsp Hbelow Hout0 Hout8 Hmap Hbuf Hbump Hstreams
      iexact Hexit
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams

end Machine

end Project.RustHashMap.CollectReserve
