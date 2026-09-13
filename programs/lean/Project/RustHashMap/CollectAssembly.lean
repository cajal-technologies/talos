import Project.RustHashMap.CollectReserve
import CodeLib.RustStd.HashMap.TableU32

/-!
# The body of `collect_entries`

Absolute `func 5`.  This module joins the five WP rules of the compiled body
into one call contract.  The rules are `twp_collect_frame`, `twp_seed_guard`
and `twp_seed_copy` in `Project.RustHashMap.CollectPrologue`,
`twp_insert_block` in `Project.RustHashMap.CollectReserve`, and
`twp_free_block`, `twp_copy_out` and `twp_restore_sp` in
`Project.RustHashMap.CollectTail`.  Together they cover instructions 0 to 58,
which is the whole body, WAT lines 853 to 973.

## Why the contract here is not `Func2Spec`

`Func2Spec` in `Project.RustHashMap.CollectContract` is the contract that the
`map_len` driver uses.  Four of its clauses are too weak for the compiled
body, so this module states `Func2SpecStrong`, which is `Func2Spec` with four
additions.

1. The body reads sixteen bytes of the data segment at 1048584 and 1048592
   and copies them into its frame as the static empty table.  `Func2Spec`
   owns no part of the data segment.  `Func2SpecStrong` takes the two cells
   and gives them back unchanged, with the values pinned to 1048576 and 0.
2. The thread-local state byte is 2 only while the thread-local is being
   dropped, and the compiled guard panics on that value.  That exit is
   neither arm of the contract, so `Func2SpecStrong` takes
   `keysBefore[16]? != some 2`.
3. Four guards inside absolute `func 17` reach a capacity-overflow panic,
   which is also neither arm.  `Func2SpecStrong` takes
   `len.toNat <= maxTableCapacity`, which kills all four.
4. The insert loop reads the pair buffer with `i32.load`, so the buffer needs
   four-byte alignment.  `Func2SpecStrong` takes `ptr.toNat % 4 = 0`.

## Two open premises

`func2_correct_of` is conditional on two arguments.

`Func14Spec` is the call contract of absolute `func 17`, the one body of the
collect path that is not proved yet.  The body calls the allocator with
alignment 8, and the allocator contract covers alignment 1 and 4 only, so
that proof waits for the alignment work in
`Project.RustHashMap.AlignPow2`.

`hsingleton` says that the two words of the static empty table are
`Table.TableAt` of `Table.empty`.  It is not provable today, because
`Table.SingletonBody` in `CodeLib.RustStd.HashMap.TableMem` also claims the
nine control bytes of `Table.empty.ctrl`, while the data segment holds eight
`\xff` bytes and the ninth address belongs to the control pointer word.
`hashbrown` never indexes the control array of the shared static singleton,
so the repair is to drop that slice from `SingletonBody`; after it, the four
header words of `tableHeader` are what the two cells give.
-/

namespace Project.RustHashMap.CollectAssembly

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
open Project.RustHashMap.CollectTail
open Project.RustHashMap.CollectPrologue
open Project.RustHashMap.CollectReserve
open scoped Wasm.SmallStep.Outcome

/-- The compiled body sits at local index 2. -/
private theorem func2_index :
    Project.RustHashMap.«module».funcs[2]? =
      some Project.RustHashMap.func2Def := by rfl

/-- The eight little-endian bytes of a `u64`. -/
private def u64Bytes (w : UInt64) : List UInt8 :=
  [u64Byte w 0, u64Byte w 1, u64Byte w 2, u64Byte w 3,
    u64Byte w 4, u64Byte w 5, u64Byte w 6, u64Byte w 7]

/-- To own a `u64` is to own its eight bytes. -/
private theorem pointsToBytes_u64Bytes [WasmHeapGS Universal.State]
    (addr : UInt32) (w : UInt64) :
    pointsToBytes 0 addr (u64Bytes w) ⊣⊢ pointsTo_u64 0 addr w := by
  have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; rfl
  have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; rfl
  have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; rfl
  have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; rfl
  have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; rfl
  have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; rfl
  simp only [u64Bytes, pointsToBytes, pointsTo_u64, e2, e3, e4, e5, e6, e7,
    (BI.sep_emp (PROP := IProp (WasmHeapGF Universal.State))).to_eq]
  exact .rfl

/-- An owned word is a byte slice of eight bytes at the same address. -/
private theorem ByteSlice_of_u64 [WasmHeapGS Universal.State]
    (addr : UInt32) (w : UInt64)
    (hbound : addr.toNat + 8 < UInt32.size) :
    pointsTo_u64 0 addr w ⊢ Slices.ByteSlice 0 addr (u64Bytes w) := by
  iintro Hword
  unfold Slices.ByteSlice
  isplitl_pureexact (show addr.toNat + (u64Bytes w).length < UInt32.size by
    simpa [u64Bytes] using hbound)
  iapply (pointsToBytes_u64Bytes addr w).mpr
  iexact Hword

/-- Eight bytes of a `u64` are eight bytes. -/
private theorem u64Bytes_length (w : UInt64) : (u64Bytes w).length = 8 := rfl

/-- Read the no-wrap fact of a slice without giving the slice up. -/
private theorem ByteSlice_bound [WasmHeapGS Universal.State]
    (addr : UInt32) (bytes : List UInt8) :
    Slices.ByteSlice (α := Universal.State) 0 addr bytes ⊢
      iprop(Slices.ByteSlice 0 addr bytes ∗
        ⌜addr.toNat + bytes.length < UInt32.size⌝) := by
  iintro Hslice
  unfold Slices.ByteSlice
  icases Hslice with ⟨%hbound, Hbytes⟩
  isplitl [Hbytes]
  · isplitl_pureexact hbound
    iexact Hbytes
  · ipureexact hbound

/-- The free block is instruction 38 of the compiled body. -/
private theorem func2_free_at_38 :
    Project.RustHashMap.func2.drop 38
      = .block 0 0 freeBlockBody :: Project.RustHashMap.func2.drop 39 := by
  rfl

def Func2SpecStrong [WasmSmallStepGS hlc Universal.State] : Prop :=
  ∀ (sp mapSlot vecHeader cap ptr len : UInt32)
    (heapId : GName) (entries : RustStd.HashMap.Map UInt32 UInt32)
    (payload spare mapBefore keysBefore below : List UInt8)
    (storedCursor : UInt32) (frontier : Nat) (history : AllocationHistory)
    (input output : List UInt8) (raised : Bool)
    {callerLocals : Locals} {stack : List Value}
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    {s : Stuckness} {E : CoPset}
    {Φ : ObservableOutcome → HeapIProp},
    CallContract 5 [.i32 vecHeader, .i32 mapSlot]
      callerLocals stack code arity remainder controls calls s E Φ iprop(
        RuntimeContext ∗
        StackPointer sp ∗
        StackBelow sp collectDepth below ∗
        Slices.ByteSlice 0 mapSlot mapBefore ∗
        pointsTo_u32 0 vecHeader cap ∗
        pointsTo_u32 0 (vecHeader + 4) ptr ∗
        pointsTo_u32 0 (vecHeader + 8) len ∗
        Slices.ByteSlice 0 ptr (payload ++ spare) ∗
        Slices.ByteSlice 0 randomStateCell keysBefore ∗
        pointsTo_u64 0 (entryStackTop + 8) 1048576 ∗
        pointsTo_u64 0 (entryStackTop + 16) 0 ∗
        BumpHeap heapId storedCursor frontier history ∗
        Streams input output raised ∗
        ⌜mapBefore.length = 32 ∧ keysBefore.length = randomStateSize ∧
          keysBefore[16]? ≠ some 2 ∧
          payload = entryCodec.serialize entries ∧
          entries.length = len.toNat ∧ len.toNat ≤ cap.toNat ∧
          len.toNat ≤ maxTableCapacity ∧
          spare.length = 8 * (cap.toNat - len.toNat) ∧
          ptr.toNat % 4 = 0 ∧
          collectDepth ≤ sp.toNat ∧ mapSlot.toNat + 32 < UInt32.size ∧
          vecHeader.toNat + 12 < UInt32.size⌝ ∗
        ((∀ k0 : UInt64, ∀ k1 : UInt64, ∀ below' : List UInt8,
            ∀ keysAfter : List UInt8, ∀ storedCursor' : UInt32,
            ∀ frontier' : Nat, ∀ history' : AllocationHistory,
            RuntimeContext -∗
            StackPointer sp -∗
            StackBelow sp collectDepth below' -∗
            RustStd.HashMap.Table.MapAt 0 mapSlot k0 k1 entries -∗
            pointsTo_u32 0 vecHeader cap -∗
            pointsTo_u32 0 (vecHeader + 4) ptr -∗
            pointsTo_u32 0 (vecHeader + 8) len -∗
            Slices.ByteSlice 0 randomStateCell keysAfter -∗
            pointsTo_u64 0 (entryStackTop + 8) 1048576 -∗
            pointsTo_u64 0 (entryStackTop + 16) 0 -∗
            BumpHeap heapId storedCursor' frontier' history' -∗
            Streams input output raised -∗
            ⌜keysAfter.length = randomStateSize ∧
              (RustStd.HashMap.Table.ofEntries
                  (RustStd.HashMap.SipHash.hashU32 k0 k1) entries).items =
                RustStd.HashMap.len (RustStd.HashMap.ofEntries entries)⌝ -∗
            ResumeWP [] callerLocals stack code arity remainder controls
              calls s E Φ) ∧
         (∀ remaining' : List UInt8,
            Streams remaining' output true -∗
              Φ (.trapped (.host OOM.trapMessage)))))

section Machine

variable [WasmSmallStepGS hlc Universal.State]

set_option maxHeartbeats 2000000 in
theorem func2_correct_of
    (hreserve : Func14Spec (hlc := hlc))
    (hsingleton : ∀ base : UInt32,
      iprop(pointsTo_u64 (α := Universal.State) 0 base 1048576 ∗
          pointsTo_u64 0 (base + 8) 0) ⊢
        HashMap.Table.TableAt 0 base HashMap.Table.empty) :
    Func2SpecStrong (hlc := hlc) := by
  unfold Func2SpecStrong CallContract callExpr
  intro sp mapSlot vecHeader cap ptr len heapId entries payload spare
    mapBefore keysBefore below storedCursor frontier history input output
    raised callerLocals stack code arity remainder controls calls s E Φ
  iintro ⟨Hruntime, Hsp, Hbelow, Hslot, Hcap, Hptr, Hlen, Hbuf, Hkeys,
    Hstatic0, Hstatic1, Hbump, Hstreams, %hfacts, Hcont⟩
  obtain ⟨hmapLength, hkeysLength, hstate, hpayload, hentriesLen, hlencap,
    hcapBound, hspare, halign, hspLow, hmapSlot, hheader⟩ := hfacts
  have hsize : UInt32.size = 4294967296 := rfl
  have hcd : collectDepth = 192 := rfl
  have hcbd : collectBelowDepth = 144 := rfl
  have hrs : randomStateSize = 24 := rfl
  have hmax : maxTableCapacity = 117440512 := rfl
  have hspLt : sp.toNat < 4294967296 := sp.toBitVec.isLt
  have hspNat : (192 : Nat) ≤ sp.toNat := by rw [hcd] at hspLow; exact hspLow
  have hframeNat : (sp - 48).toNat = sp.toNat - 48 := by
    rw [UInt32.toNat_sub_of_le sp 48
      (UInt32.le_iff_toNat_le.mpr
        (by simpa using (by omega : (48 : Nat) ≤ sp.toNat)))]
    rfl
  have hpayloadLen : payload.length = 8 * entries.length := by
    rw [hpayload, serialize_eq_pairWords,
      WordCodec.u32le_serialize_length, pairWords_length]
    omega
  have hpaywords : payload = WordCodec.u32le.serialize (pairWords entries) :=
    hpayload.trans (serialize_eq_pairWords entries)
  have h30 : (2 : Nat) ^ 30 = 1073741824 := by norm_num
  have hcut : collectDepth - 48 = collectBelowDepth := rfl
  have hbase : sp - UInt32.ofNat 48 = sp - 48 := rfl
  have hrestore : sp - 48 + 48 = sp := UInt32.sub_add_cancel sp 48
  have l8 : sp - 48 + UInt32.ofNat 8 = sp - 48 + 8 := rfl
  have l16 : sp - 48 + UInt32.ofNat 16 = sp - 48 + 16 := rfl
  have b24 : sp - 48 + 16 + 8 = sp - 48 + 24 := by rw [UInt32.add_assoc]; rfl
  have b32 : sp - 48 + 16 + 16 = sp - 48 + 32 := by rw [UInt32.add_assoc]; rfl
  have b40 : sp - 48 + 16 + 24 = sp - 48 + 40 := by rw [UInt32.add_assoc]; rfl
  have m24 : sp - 48 + 16 + UInt32.ofNat 8 = sp - 48 + 24 := by
    rw [UInt32.add_assoc]; rfl
  have m32 : sp - 48 + 24 + UInt32.ofNat 8 = sp - 48 + 32 := by
    rw [UInt32.add_assoc]; rfl
  have m40 : sp - 48 + 32 + UInt32.ofNat 8 = sp - 48 + 40 := by
    rw [UInt32.add_assoc]; rfl
  have hk8 : randomStateCell + UInt32.ofNat 8 = randomStateCell + 8 := rfl
  have hk16 : randomStateCell + UInt32.ofNat 16 = randomStateCell + 16 := rfl
  have e8 : (sp - 48 + 8).toNat = (sp - 48).toNat + 8 := by
    simpa using Slices.byteOffset_toNat (sp - 48) 8 (by omega)
  have e16 : (sp - 48 + 16).toNat = (sp - 48).toNat + 16 := by
    simpa using Slices.byteOffset_toNat (sp - 48) 16 (by omega)
  have e24 : (sp - 48 + 24).toNat = (sp - 48).toNat + 24 := by
    simpa using Slices.byteOffset_toNat (sp - 48) 24 (by omega)
  have e32 : (sp - 48 + 32).toNat = (sp - 48).toNat + 32 := by
    simpa using Slices.byteOffset_toNat (sp - 48) 32 (by omega)
  have e40 : (sp - 48 + 40).toNat = (sp - 48).toNat + 40 := by
    simpa using Slices.byteOffset_toNat (sp - 48) 40 (by omega)
  ihave ⟨Hbuf, %hbufBound⟩ := ByteSlice_bound ptr (payload ++ spare) $$ Hbuf
  have hptrBound : ptr.toNat + 8 * entries.length < UInt32.size := by
    rw [List.length_append, hpayloadLen] at hbufBound
    omega
  iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
  simp only [List.cons_append, List.nil_append]
  wasm_twp_rebind Wasm.SmallStep.twp_call Project.RustHashMap.«module» 5
      Project.RustHashMap.func2Def (by decide) func2_index with Hmodule
  simp [Project.RustHashMap.func2Def, Function.toLocals,
    Function.numParams, ValueType.zero]
  iclose_map_runtime Hruntime with Hmodule Henv
  rw [Project.RustHashMap.CollectPrologue.func2_frame]
  iapply twp_collect_frame (hheader := hheader)
  isplitl_exacts [Hsp Hbelow Hcap Hptr Hlen]
  · iintro Hsp Hbelow Hframe Hcap Hptr Hlen %hframeLength
    rw [Project.RustHashMap.CollectPrologue.func2_seed_guard]
    iapply twp_seed_guard (mapSlot := mapSlot) (cap := cap)
      (frame := sp - 48) (cur := len) (ptr := ptr) (endAddr := 0)
      (seed0 := 0) (keysBefore := keysBefore)
      (lower := below.take collectBelowDepth)
      (hkeysLength := hkeysLength) (hstate := hstate)
      (hframe := by omega)
    isplitl_exacts [Hruntime Hsp Hbelow Hkeys Hbump Hstreams]
    isplit
    · iintro %k0 %k1 %tail %lower' %storedCursor' %frontier' %history'
      iintro Hruntime Hsp Hbelow Hkey0 Hkey1 Htail Hbump Hstreams
        %htailLength
      -- the 48 frame bytes as two out slots and four cells
      ihave ⟨Hlow, Hhigh⟩ :=
        ByteSlice_cut (sp - 48) (below.drop collectBelowDepth) 16
          (by omega) $$ Hframe
      isimp only [l16] at Hhigh
      ihave ⟨Hout0, Hout8⟩ :=
        ByteSlice_cut (sp - 48) ((below.drop collectBelowDepth).take 16) 8
          (by rw [List.length_take]; omega) $$ Hlow
      isimp only [l8] at Hout8
      ihave ⟨%f16, %f24, %f32, %f40, Hc16, Hc24, Hc32, Hc40⟩ :=
        ByteSlice_thirtyTwo_as_cells 0 (sp - 48 + 16)
          ((below.drop collectBelowDepth).drop 16)
          (by rw [List.length_drop]; omega) $$ Hhigh
      isimp only [b24] at Hc24
      isimp only [b32] at Hc32
      isimp only [b40] at Hc40
      rw [Project.RustHashMap.CollectPrologue.func2_seed_copy]
      iapply twp_seed_copy (mapSlot := mapSlot) (cap := cap)
        (frame := sp - 48) (cur := len) (ptr := ptr) (endAddr := 0)
        (seed0 := 0) (k0 := k0) (k1 := k1) (d0 := 1048576) (d1 := 0)
        (f16 := f16) (f24 := f24) (f32 := f32) (f40 := f40)
        (hframe := by omega)
      isplitl_exacts [Hkey0 Hkey1 Hstatic0 Hstatic1 Hc16 Hc24 Hc32 Hc40]
      iintro ⟨Hkey0, Hkey1, Hstatic0, Hstatic1, Hd0, Hd1, Hs32, Hs40⟩
      -- the static empty table is the frame table
      isimp only [← b24] at Hd1
      ihave Htable := hsingleton (sp - 48 + 16) $$ [Hd0 Hd1]
      · iframe Hd0 Hd1
      ihave Hout0 : OutSlot (sp - 48) $$ [Hout0]
      · isimp only [OutSlot]
        iexists ((below.drop collectBelowDepth).take 16).take 8
        isplitl_pureexact
          (show (((below.drop collectBelowDepth).take 16).take 8).length = 8 by
            rw [List.length_take, List.length_take]; omega)
        iexact Hout0
      ihave Hout8 : OutSlot (sp - 48 + 8) $$ [Hout8]
      · isimp only [OutSlot]
        iexists ((below.drop collectBelowDepth).take 16).drop 8
        isplitl_pureexact
          (show (((below.drop collectBelowDepth).take 16).drop 8).length = 8 by
            rw [List.length_drop, List.length_take]; omega)
        iexact Hout8
      -- the pair buffer as words
      ihave ⟨Hpay, Hspare⟩ :=
        (Slices.ByteSlice_append 0 ptr payload spare).mp $$ Hbuf
      ihave Hwords :=
        (Slices.ByteSlice_serialize_as_WordSlice 0 ptr (pairWords entries)
          halign).mp $$ [Hpay]
      · irw_exact [hpaywords] with Hpay
      -- the reserve and the insert loop
      rw [func2_reserve_block]
      iapply twp_insert_block hreserve (mapSlot := mapSlot) (cap := cap)
        (frame := sp - 48) (ptr := ptr) (endAddr0 := 0) (len := len)
        (seed := k0) (k0 := k0) (k1 := k1) (entries := entries)
        (lower := lower') (hlen := hentriesLen) (hcap := hcapBound)
        (hptr := hptrBound) (hdepth := by omega) (hframe := by omega)
      isplitl_exacts [Hruntime Hsp Hbelow Hout0 Hout8 Htable Hs32 Hs40 Hwords
        Hbump Hstreams]
      isplit
      · iintro %cur2 %endAddr2 %lower2 %storedCursor2 %frontier2 %history2
        iintro Hruntime Hsp Hbelow Hout0 Hout8 Hmap Hwords Hbump Hstreams
        -- the free of the pair buffer
        rw [func2_free_at_38]
        iapply twp_free_block
        isplitl_exact Hruntime
        · iintro Hruntime
          -- the copy out
          rw [func2_copy_out]
          iapply twp_copy_out (mapSlot := mapSlot) (cap := cap)
            (frame := sp - 48) (cur := cur2) (ptr := ptr)
            (endAddr := endAddr2) (seed := k0) (k0 := k0) (k1 := k1)
            (t := HashMap.Table.ofEntries
              (HashMap.SipHash.hashU32 k0 k1) entries)
            (mapBefore := mapBefore) (hmapLength := hmapLength)
            (hmapSlot := hmapSlot) (hframe := by omega)
          isplitl_exacts [Hslot Hmap]
          · iintro Hmapout Hsrc
            icases Hsrc with ⟨%g0, %g1, Hg16, Hg24, Hg32, Hg40⟩
            -- the epilogue and the return
            iopen_map_runtime Hruntime with ⟨Hmodule, Henv⟩
            rw [func2_epilogue]
            iapply twp_restore_sp
            isplitl_exact Hsp
            · iintro Hsp
              isimp only [hrestore] at Hsp
              wasm_twp_rebind twp_returnFromCallFallthrough with Hmodule
              simp only [List.take_zero, List.nil_append]
              -- rebuild the frame bytes
              isimp only [OutSlot] at Hout0 Hout8
              icases Hout0 with ⟨%o0, %ho0, Hout0⟩
              icases Hout8 with ⟨%o8, %ho8, Hout8⟩
              ihave Hb16 :=
                ByteSlice_of_u64 (sp - 48 + 16) g0 (by omega) $$ Hg16
              ihave Hb24 :=
                ByteSlice_of_u64 (sp - 48 + 24) g1 (by omega) $$ Hg24
              ihave Hb32 :=
                ByteSlice_of_u64 (sp - 48 + 32) k0 (by omega) $$ Hg32
              ihave Hb40 :=
                ByteSlice_of_u64 (sp - 48 + 40) k1 (by omega) $$ Hg40
              ihave Hj32 :=
                ByteSlice_glue (sp - 48 + 32) (u64Bytes k0) (u64Bytes k1) 8
                  (u64Bytes_length k0) $$ [Hb32 Hb40]
              · isplitl_exact Hb32
                · irw_exact [m40] with Hb40
              ihave Hj24 :=
                ByteSlice_glue (sp - 48 + 24) (u64Bytes g1)
                  (u64Bytes k0 ++ u64Bytes k1) 8 (u64Bytes_length g1) $$
                  [Hb24 Hj32]
              · isplitl_exact Hb24
                · irw_exact [m32] with Hj32
              ihave Hj16 :=
                ByteSlice_glue (sp - 48 + 16) (u64Bytes g0)
                  (u64Bytes g1 ++ (u64Bytes k0 ++ u64Bytes k1)) 8
                  (u64Bytes_length g0) $$ [Hb16 Hj24]
              · isplitl_exact Hb16
                · irw_exact [m24] with Hj24
              ihave Hj0 :=
                ByteSlice_glue (sp - 48) o0 o8 8 ho0 $$ [Hout0 Hout8]
              · isplitl_exact Hout0
                · irw_exact [l8] with Hout8
              ihave Hframe :=
                ByteSlice_glue (sp - 48) (o0 ++ o8)
                  (u64Bytes g0 ++
                    (u64Bytes g1 ++ (u64Bytes k0 ++ u64Bytes k1))) 16
                  (by rw [List.length_append, ho0, ho8]) $$ [Hj0 Hj16]
              · isplitl_exact Hj0
                · irw_exact [l16] with Hj16
              ihave Hframe :=
                StackBelow_intro sp (sp - 48) 48
                  (o0 ++ o8 ++
                    (u64Bytes g0 ++
                      (u64Bytes g1 ++ (u64Bytes k0 ++ u64Bytes k1))))
                  (by
                    rw [List.length_append, List.length_append,
                      List.length_append, List.length_append,
                      List.length_append, ho0, ho8, u64Bytes_length,
                      u64Bytes_length, u64Bytes_length, u64Bytes_length])
                  hbase $$ Hframe
              ihave ⟨Hbelow, %hlower2Length⟩ :=
                StackBelow_length (sp - 48) collectBelowDepth lower2 $$ Hbelow
              isimp only [← hbase, ← hcut] at Hbelow
              ihave Hbelow :=
                frame_join sp collectDepth 48 lower2
                  (o0 ++ o8 ++
                    (u64Bytes g0 ++
                      (u64Bytes g1 ++ (u64Bytes k0 ++ u64Bytes k1))))
                  (by rw [hcut]; exact hlower2Length) (by decide) $$
                  [Hbelow Hframe]
              · isplitl_exact Hbelow
                · iexact Hframe
              -- rebuild the thread-local region
              ihave Hkb0 :=
                ByteSlice_of_u64 randomStateCell (k0 + 1) (by decide) $$ Hkey0
              ihave Hkb1 :=
                ByteSlice_of_u64 (randomStateCell + 8) k1 (by decide) $$ Hkey1
              ihave Hkeys :=
                ByteSlice_glue randomStateCell (u64Bytes (k0 + 1))
                  (u64Bytes k1) 8 (u64Bytes_length (k0 + 1)) $$ [Hkb0 Hkb1]
              · isplitl_exact Hkb0
                · irw_exact [hk8] with Hkb1
              ihave Hkeys :=
                ByteSlice_glue randomStateCell
                  (u64Bytes (k0 + 1) ++ u64Bytes k1) tail 16
                  (by rw [List.length_append, u64Bytes_length,
                    u64Bytes_length]) $$ [Hkeys Htail]
              · isplitl_exact Hkeys
                · irw_exact [hk16] with Htail
              -- the map value
              ihave Hmapout : HashMap.Table.MapAt 0 mapSlot k0 k1 entries $$
                [Hmapout]
              · isimp only [HashMap.Table.MapAt]
                iexact Hmapout
              iclose_map_runtime Hruntime with Hmodule Henv
              have hcount :
                  (HashMap.Table.ofEntries
                    (HashMap.SipHash.hashU32 k0 k1) entries).items
                    = HashMap.len (HashMap.ofEntries entries) :=
                HashMap.Table.len_ofEntries_u32 k0 k1 entries (by omega)
              have hkeysAfter :
                  (u64Bytes (k0 + 1) ++ u64Bytes k1 ++ tail).length
                    = randomStateSize := by
                rw [List.length_append, List.length_append, htailLength,
                  u64Bytes_length, u64Bytes_length, hrs]
              ihave Hnormal := BI.and_elim_l $$ Hcont
              ihave Hnormal := Hnormal $$ %k0 %k1
                %(lower2 ++
                  (o0 ++ o8 ++
                    (u64Bytes g0 ++
                      (u64Bytes g1 ++ (u64Bytes k0 ++ u64Bytes k1)))))
                %(u64Bytes (k0 + 1) ++ u64Bytes k1 ++ tail)
                %storedCursor2 %frontier2 %history2
              isimp only [ResumeWP, resumeExpr, List.nil_append] at Hnormal
              iapply Hnormal $$ Hruntime Hsp Hbelow Hmapout Hcap Hptr Hlen
                Hkeys Hstatic0 Hstatic1 Hbump Hstreams %⟨hkeysAfter, hcount⟩
      · iintro %remaining' Hstreams
        ihave Hoom := BI.and_elim_r $$ Hcont
        ihave Hoom := Hoom $$ %remaining'
        iapply Hoom $$ Hstreams
    · iintro %remaining' Hstreams
      ihave Hoom := BI.and_elim_r $$ Hcont
      ihave Hoom := Hoom $$ %remaining'
      iapply Hoom $$ Hstreams

end Machine

end Project.RustHashMap.CollectAssembly
