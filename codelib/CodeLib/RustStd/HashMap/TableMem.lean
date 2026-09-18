import CodeLib.SepLogic.BorshSlice
import CodeLib.RustStd.HashMap.Swar

/-!
# The `hashbrown` table as owned wasm memory

`CodeLib.RustStd.HashMap.Table` is a pure model of one `RawTable<(K, V)>`.
This file states what the compiled `rust_hash_map` module keeps in linear
memory for a `Table UInt32 UInt32`, as separation-logic ownership over
`CodeLib.SepLogic.ByteSlice`, and it proves the lemmas that turn one memory
access of the compiled code into one step of the model.

## Layout

The layout is the one `hashbrown` 0.16.1 uses on wasm32 and the compiled
code of `rust_hash_map` confirms it:

* `RawTableInner` is four words: `ctrl`, `bucket_mask`, `growth_left`,
  `items`, at offsets 0, 4, 8 and 12 of the map value.  `bucket_mask` is
  `buckets - 1`.
* `ctrl` points at `buckets + 8` control bytes.  A group read is one
  `i64.load align=1` of the eight bytes at `ctrl + pos`.
* Bucket `i` holds one `(u32, u32)` pair of eight bytes at
  `ctrl - 8 * (i + 1)`, the key first.  The compiled code computes this
  address as `ctrl - (i << 3) + 0xFFFFFFF8`.
* A table with `bucket_mask = 0` is the singleton table: `ctrl` points at
  the static empty group and no bucket is allocated.

## Contents

* `u64Byte_groupWord`: byte `k` of the group word is byte `k` of the
  group.  With it, `pointsToBytes_eight_as_u64` turns eight owned bytes
  into one owned `u64` that holds `groupWord` of those bytes, and
  `ByteSlice_groupAt` focuses the group at `pos` inside the control bytes
  of a table.  The SWAR theorems of `CodeLib.RustStd.HashMap.Swar` then
  speak about the loaded word.
* `slotCell` and `slotsBefore`: the bucket pairs below `ctrl`.
  `slotsBefore_focus` isolates bucket `i` and `slotsBefore_set` puts a new
  pair in it.
* `tableHeader`, `TableBody`, `SingletonBody` and `TableAt`: the
  representation predicate of a table.
* The address bridges `bucketAddr_of_wasm`, `and_mask_toNat` and
  `h2_toUInt64`: the bucket address, the masked probe position and the
  repeated tag of the compiled code equal the ones of the model.

The lemmas here are structural.  They do not run the compiled code.  The
proofs of the probe loop, of `insert` and of `remove` against the compiled
bodies are the consumers.

Overlap note: upstream PR #235 adds `CodeLib.SepLogic.PointsToBytesSlice`.
Its `pointsTo_u64_as_bytes` states a `u64` as its eight `u64Byte`s.  Its
`pointsToBytes_focus_u64` is the closest analogue of
`pointsToBytes_eight_as_u64` here, which starts from eight arbitrary bytes
and names the word `groupWord`.  Its `pointsToBytes_slice` over a byte
window is the closest analogue of `ByteSlice_window` here, which is a
corollary of `ByteSlice_append` at the `ByteSlice` level.  Its
`pointsToBytes_focus` borrows one byte.  When that PR merges, both can be
re-based on it in place.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.SepLogic Wasm.SepLogic.Slices Iris Std

/-! ## Bytes of a group word -/

/-- Bit `i` of the packed word is bit `i % 8` of byte `i / 8`, for a list
of at most eight bytes.  Bytes beyond the list read as zero. -/
theorem u64OfBytesLE_testBit (g : List UInt8) (hg : g.length ≤ 8) (i : Nat) :
    (SipHash.u64OfBytesLE g).toNat.testBit i =
      (g.getD (i / 8) 0).toNat.testBit (i % 8) := by
  induction g generalizing i with
  | nil =>
    simp [SipHash.u64OfBytesLE]
  | cons b rest ih =>
    simp only [SipHash.u64OfBytesLE, List.foldr] at ih ⊢
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, Nat.testBit_or, Nat.testBit_mod_two_pow,
      Nat.testBit_shiftLeft, UInt8.toNat_toUInt64, show (8 : UInt64).toNat % 64 = 8 from rfl]
    have hrest : rest.length ≤ 8 := by simp at hg; omega
    by_cases hi : i < 8
    · have h8 : ¬ (i ≥ 8) := by omega
      simp [h8, Nat.div_eq_of_lt hi, Nat.mod_eq_of_lt hi]
    · have h8 : i ≥ 8 := by omega
      have hb : b.toNat.testBit i = false :=
        Nat.testBit_lt_two_pow
          (Nat.lt_of_lt_of_le (UInt8.toNat_lt b) (Nat.pow_le_pow_right (by decide) h8))
      rw [hb, ih hrest (i - 8)]
      have hdiv : i / 8 = (i - 8) / 8 + 1 := by omega
      have hmod : i % 8 = (i - 8) % 8 := by omega
      rw [hdiv, hmod, List.getD_cons_succ]
      by_cases h64 : i < 64
      · simp [h64, h8]
      · have hout : rest.length ≤ (i - 8) / 8 := by simp at hg; omega
        rw [List.getD_eq_default _ _ hout]
        simp [h64]

/-- Byte `k` of the packed word of eight bytes is byte `k` of the list. -/
theorem u64Byte_u64OfBytesLE (g : List UInt8) (hg : g.length = 8) (k : Nat) (hk : k < 8) :
    u64Byte (SipHash.u64OfBytesLE g) k = g.getD k 0 := by
  have hshift : u64Byte (SipHash.u64OfBytesLE g) k =
      (SipHash.u64OfBytesLE g >>> (8 * UInt64.ofNat k)).toUInt8 := by
    match k, hk with
    | 0, _ => simp [u64Byte]
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
  rw [hshift]
  apply UInt8.toNat_inj.mp
  apply Nat.eq_of_testBit_eq
  intro m
  rw [UInt64.toNat_toUInt8, Nat.testBit_mod_two_pow, UInt64.toNat_shiftRight,
    Nat.testBit_shiftRight, u64OfBytesLE_testBit g (by omega)]
  have hkN : (UInt64.ofNat k).toNat = k :=
    UInt64.toNat_ofNat_of_lt (by simp only [UInt64.size]; omega)
  have hk' : (8 * UInt64.ofNat k).toNat % 64 = 8 * k := by
    rw [UInt64.toNat_mul, hkN]
    simp only [show (8 : UInt64).toNat = 8 from rfl]
    rw [Nat.mod_eq_of_lt (by omega : 8 * k < 2 ^ 64), Nat.mod_eq_of_lt (by omega)]
  rw [hk']
  by_cases hm : m < 8
  · have hdiv : (8 * k + m) / 8 = k := by omega
    have hmod : (8 * k + m) % 8 = m := by omega
    simp [hm, hdiv, hmod]
  · have hout : (g.getD k 0).toNat.testBit m = false :=
      Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le (UInt8.toNat_lt _) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hout]
    simp [hm]

/-- Byte `k` of `Group::load` of a group is control byte `k` of the group. -/
theorem u64Byte_groupWord (g : List UInt8) (hg : g.length = 8) (k : Nat) (hk : k < 8) :
    u64Byte (groupWord g) k = g.getD k 0 :=
  u64Byte_u64OfBytesLE g hg k hk

/-- The group at `pos` is the window of eight physical control bytes at
`pos`, when the window fits. -/
theorem groupAt_eq_take_drop {K V : Type} (t : Table K V) {pos : Nat}
    (hpos : pos + 8 ≤ t.ctrl.length) :
    groupAt t pos = (t.ctrl.drop pos).take 8 := by
  apply List.ext_getElem
  · simp only [groupAt, List.length_map, List.length_range, List.length_take,
      List.length_drop]
    omega
  · intro j hj hj'
    simp only [groupAt, List.getElem_map, List.getElem_range, List.getElem_take,
      List.getElem_drop, ctrlAt, List.getD_eq_getElem?_getD]
    have hlt : pos + j < t.ctrl.length := by
      simp only [groupAt, List.length_map, List.length_range] at hj; omega
    rw [List.getElem?_eq_getElem hlt]
    rfl

/-! ## The wasm arithmetic of the compiled code -/

/-- `ctrl - (i << 3) + 0xFFFFFFF8`, the bucket address the compiled code
computes, is `ctrl - 8 * (i + 1)`. -/
theorem bucketAddr_of_wasm (ctrl idx : UInt32) :
    ctrl - (idx <<< 3) + 4294967288 = ctrl - UInt32.ofNat (8 * (idx.toNat + 1)) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_sub, UInt32.toNat_add, UInt32.toNat_shiftLeft, UInt32.toNat_ofNat',
    Nat.shiftLeft_eq, UInt32.toNat_ofNat, Nat.reduceMod, Nat.reducePow]
  have := UInt32.toNat_lt idx
  have := UInt32.toNat_lt ctrl
  omega

/-- `x & bucket_mask` is `x % buckets` when `buckets = 2 ^ m`. -/
theorem and_mask_toNat (x : UInt32) {m : Nat} (hm : m ≤ 32) :
    (x &&& UInt32.ofNat (2 ^ m - 1)).toNat = x.toNat % 2 ^ m := by
  have hle : 2 ^ m ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hm
  rw [UInt32.toNat_and, UInt32.toNat_ofNat_of_lt' (by simp only [UInt32.size]; omega),
    Nat.and_two_pow_sub_one_eq_mod]

/-- The masked low word of the hash is the start position of the probe
sequence of the model. -/
theorem probeStart_pos_of_wasm {K V : Type} (t : Table K V) {m : Nat} (hm : m ≤ 32)
    (hb : t.buckets = 2 ^ m) (hash : UInt64) :
    (hash.toUInt32 &&& UInt32.ofNat (t.buckets - 1)).toNat = (probeStart t hash).pos := by
  rw [probeStart, h1, hb, and_mask_toNat _ hm, UInt64.toNat_toUInt32]

/-- `(hash >> 25) & 0x7f` as the compiled code keeps it, is the tag `h2`. -/
theorem h2_toUInt64 (hash : UInt64) :
    (h2 hash).toUInt64 = (hash >>> 25) &&& 127 := by
  apply UInt64.toNat_inj.mp
  rw [h2, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8, UInt64.toNat_and]
  have h : (hash >>> 25).toNat &&& (127 : UInt64).toNat = (hash >>> 25).toNat % 2 ^ 7 := by
    rw [show (127 : UInt64).toNat = 2 ^ 7 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
  rw [h]
  omega

/-- Two subtractions of a wasm address are one subtraction of the sum. -/
theorem sub_sub_addr (a b c : UInt32) : a - b - c = a - (b + c) := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_sub, UInt32.toNat_add]
  have := UInt32.toNat_lt a
  have := UInt32.toNat_lt b
  have := UInt32.toNat_lt c
  omega

/-! ## Ownership -/

section Ownership

variable {α : Type} [WasmHeapGS α]

/-- To own four bytes is to own the word they encode, with no bound. -/
theorem pointsToBytes_four_as_u32 (memId : Nat) (addr : UInt32) (bytes : List UInt8)
    (hlength : bytes.length = 4) :
    pointsToBytes (α := α) memId addr bytes ⊣⊢
      pointsTo_u32 memId addr (WordCodec.decodeU32 bytes) := by
  refine (pointsTo_u32_as_bytes memId addr (WordCodec.decodeU32 bytes)).trans ?_ |>.symm
  rw [← encodeU32_eq_u32Bytes, encodeU32_decodeU32_of_length bytes hlength]
  exact .rfl

/-- To own eight bytes is to own the group word they pack. -/
theorem pointsToBytes_eight_as_u64 (memId : Nat) (addr : UInt32) (g : List UInt8)
    (hg : g.length = 8) :
    pointsToBytes (α := α) memId addr g ⊣⊢ pointsTo_u64 memId addr (groupWord g) := by
  match g, hg with
  | [b0, b1, b2, b3, b4, b5, b6, b7], _ =>
    have h0 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 0 (by decide)
    have h1 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 1 (by decide)
    have h2 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 2 (by decide)
    have h3 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 3 (by decide)
    have h4 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 4 (by decide)
    have h5 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 5 (by decide)
    have h6 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 6 (by decide)
    have h7 := u64Byte_groupWord [b0, b1, b2, b3, b4, b5, b6, b7] rfl 7 (by decide)
    simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7
    have e2 : addr + 1 + 1 = addr + 2 := by rw [UInt32.add_assoc]; rfl
    have e3 : addr + 2 + 1 = addr + 3 := by rw [UInt32.add_assoc]; rfl
    have e4 : addr + 3 + 1 = addr + 4 := by rw [UInt32.add_assoc]; rfl
    have e5 : addr + 4 + 1 = addr + 5 := by rw [UInt32.add_assoc]; rfl
    have e6 : addr + 5 + 1 = addr + 6 := by rw [UInt32.add_assoc]; rfl
    have e7 : addr + 6 + 1 = addr + 7 := by rw [UInt32.add_assoc]; rfl
    simp only [pointsToBytes, pointsTo_u64, e2, e3, e4, e5, e6, e7, h0, h1, h2, h3, h4, h5, h6,
      h7, (BI.sep_emp (PROP := IProp (WasmHeapGF α))).to_eq]
    exact .rfl

/-- A slice of eight bytes is a bound and the group word. -/
theorem ByteSlice_eight_as_u64 (memId : Nat) (ptr : UInt32) (g : List UInt8)
    (hg : g.length = 8) :
    Slices.ByteSlice (α := α) memId ptr g ⊣⊢
      iprop(⌜ptr.toNat + 8 < UInt32.size⌝ ∗ pointsTo_u64 memId ptr (groupWord g)) := by
  unfold Slices.ByteSlice
  rw [hg]
  exact BI.sep_congr .rfl (pointsToBytes_eight_as_u64 memId ptr g hg)

/-- A slice splits into a prefix, a window of `count` bytes at `pos`, and
the rest. -/
theorem ByteSlice_window (memId : Nat) (ptr : UInt32) (bytes : List UInt8)
    (pos count : Nat) (hfit : pos + count ≤ bytes.length) :
    Slices.ByteSlice (α := α) memId ptr bytes ⊣⊢
      iprop(Slices.ByteSlice memId ptr (bytes.take pos) ∗
        Slices.ByteSlice memId (ptr + UInt32.ofNat pos) ((bytes.drop pos).take count) ∗
        Slices.ByteSlice memId (ptr + UInt32.ofNat (pos + count)) (bytes.drop (pos + count))) := by
  have hsplit : bytes = bytes.take pos ++ ((bytes.drop pos).take count ++
      bytes.drop (pos + count)) := by
    rw [← List.drop_drop, List.take_append_drop, List.take_append_drop]
  have hprefix : (bytes.take pos).length = pos := by
    rw [List.length_take]; omega
  have hwindow : ((bytes.drop pos).take count).length = count := by
    rw [List.length_take, List.length_drop]; omega
  have haddr : ptr + UInt32.ofNat pos + UInt32.ofNat count = ptr + UInt32.ofNat (pos + count) := by
    rw [UInt32.ofNat_add, UInt32.add_assoc]
  conv_lhs => rw [hsplit]
  refine (ByteSlice_append memId ptr _ _).trans ?_
  rw [hprefix]
  refine BI.sep_congr .rfl ?_
  refine (ByteSlice_append memId _ _ _).trans ?_
  rw [hwindow, haddr]
  exact .rfl

/-- The group at `pos` of the control bytes, as one owned `u64`. -/
theorem ByteSlice_groupAt {K V : Type} (memId : Nat) (ctrl : UInt32) (t : Table K V)
    {pos : Nat} (hpos : pos + 8 ≤ t.ctrl.length) :
    Slices.ByteSlice (α := α) memId ctrl t.ctrl ⊣⊢
      iprop(Slices.ByteSlice memId ctrl (t.ctrl.take pos) ∗
        (⌜(ctrl + UInt32.ofNat pos).toNat + 8 < UInt32.size⌝ ∗
          pointsTo_u64 memId (ctrl + UInt32.ofNat pos) (groupWord (groupAt t pos))) ∗
        Slices.ByteSlice memId (ctrl + UInt32.ofNat (pos + 8)) (t.ctrl.drop (pos + 8))) := by
  rw [groupAt_eq_take_drop t hpos]
  refine (ByteSlice_window memId ctrl t.ctrl pos 8 hpos).trans ?_
  refine BI.sep_congr .rfl (BI.sep_congr ?_ .rfl)
  exact ByteSlice_eight_as_u64 memId _ _ (by rw [List.length_take, List.length_drop]; omega)

/-- The one group of the static singleton, as one owned `u64`.  The
singleton owns the first eight control bytes only, so the group at zero
is the whole slice. -/
theorem ByteSlice_singleton_group {K V : Type} (memId : Nat) (ctrl : UInt32)
    (t : Table K V) (hlen : 8 ≤ t.ctrl.length) :
    Slices.ByteSlice (α := α) memId ctrl (t.ctrl.take 8) ⊣⊢
      iprop(⌜ctrl.toNat + 8 < UInt32.size⌝ ∗
        pointsTo_u64 memId ctrl (groupWord (groupAt t 0))) := by
  have hgroup : groupAt t 0 = t.ctrl.take 8 := by
    rw [groupAt_eq_take_drop t (by omega), List.drop_zero]
  rw [hgroup]
  exact ByteSlice_eight_as_u64 memId ctrl _
    (by rw [List.length_take]; omega)

/-- One control byte of the control bytes, as one owned byte. -/
theorem ByteSlice_ctrlAt {K V : Type} (memId : Nat) (ctrl : UInt32) (t : Table K V)
    {i : Nat} (hi : i < t.ctrl.length) :
    Slices.ByteSlice (α := α) memId ctrl t.ctrl ⊣⊢
      iprop(Slices.ByteSlice memId ctrl (t.ctrl.take i) ∗
        (⌜(ctrl + UInt32.ofNat i).toNat + 1 < UInt32.size⌝ ∗
          (⟨memId, ctrl + UInt32.ofNat i⟩ ↦w ctrlAt t i)) ∗
        Slices.ByteSlice memId (ctrl + UInt32.ofNat (i + 1)) (t.ctrl.drop (i + 1))) := by
  refine (ByteSlice_window memId ctrl t.ctrl i 1 hi).trans ?_
  refine BI.sep_congr .rfl (BI.sep_congr ?_ .rfl)
  have hbyte : (t.ctrl.drop i).take 1 = [ctrlAt t i] := by
    rw [List.drop_eq_getElem_cons hi, List.take_succ_cons, List.take_zero, ctrlAt,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  rw [hbyte]
  exact ByteSlice_singleton memId _ _

/-! ## Buckets -/

/-- The address of bucket `i`: `8 * (i + 1)` bytes below `ctrl`. -/
def bucketAddr (ctrl : UInt32) (i : Nat) : UInt32 :=
  ctrl - UInt32.ofNat (8 * (i + 1))

/-- One bucket of eight bytes: a full slot holds the key then the value, an
empty or deleted slot holds eight bytes with no defined content. -/
def slotCell (memId : Nat) (addr : UInt32) :
    Option (UInt32 × UInt32) → IProp (WasmHeapGF α)
  | some (key, value) =>
      iprop(pointsTo_u32 memId addr key ∗ pointsTo_u32 memId (addr + 4) value)
  | none =>
      iprop(∃ bytes : List UInt8, ⌜bytes.length = 8⌝ ∗ pointsToBytes memId addr bytes)

/-- The buckets below `ctrl`, each one lower than the one before it: slot
`i` of the list is at `ctrl - 8 * (i + 1)`. -/
def slotsBefore (memId : Nat) (ctrl : UInt32) :
    List (Option (UInt32 × UInt32)) → IProp (WasmHeapGF α)
  | [] => iprop(emp)
  | slot :: rest =>
      iprop(slotCell memId (ctrl - 8) slot ∗ slotsBefore memId (ctrl - 8) rest)

/-- A full slot is eight bytes with no defined content, when the proof
forgets the pair.  `erase` uses this direction. -/
theorem slotCell_forget (memId : Nat) (addr : UInt32) (key value : UInt32) :
    slotCell (α := α) memId addr (some (key, value)) ⊢ slotCell memId addr none := by
  simp only [slotCell]
  iintro ⟨Hkey, Hvalue⟩
  iexists [u32Byte key 0, u32Byte key 1, u32Byte key 2, u32Byte key 3,
    u32Byte value 0, u32Byte value 1, u32Byte value 2, u32Byte value 3]
  isplitl_pureexact rfl
  have happ := pointsToBytes_append (α := α) memId addr
    [u32Byte key 0, u32Byte key 1, u32Byte key 2, u32Byte key 3]
    [u32Byte value 0, u32Byte value 1, u32Byte value 2, u32Byte value 3]
  rw [show addr + UInt32.ofNat [u32Byte key 0, u32Byte key 1, u32Byte key 2, u32Byte key 3].length =
    addr + 4 from rfl] at happ
  simp only [List.cons_append, List.nil_append] at happ
  iapply happ.mpr
  isplitl [Hkey]
  · iapply (pointsTo_u32_as_bytes memId addr key).mp
    iexact Hkey
  · iapply (pointsTo_u32_as_bytes memId (addr + 4) value).mp
    iexact Hvalue

/-- An empty slot holds some key word and some value word.  `insert`
writes both. -/
theorem slotCell_none_as_words (memId : Nat) (addr : UInt32) :
    slotCell (α := α) memId addr none ⊣⊢
      iprop(∃ key : UInt32, ∃ value : UInt32,
        pointsTo_u32 memId addr key ∗ pointsTo_u32 memId (addr + 4) value) := by
  constructor
  · simp only [slotCell]
    iintro ⟨%bytes, %hlength, Hbytes⟩
    have hhead : (bytes.take 4).length = 4 := by rw [List.length_take]; omega
    have htail : (bytes.drop 4).length = 4 := by rw [List.length_drop]; omega
    have happ : pointsToBytes (α := α) memId addr bytes ⊢
        pointsToBytes memId addr (bytes.take 4) ∗ pointsToBytes memId (addr + 4) (bytes.drop 4) := by
      have h := (pointsToBytes_append (α := α) memId addr (bytes.take 4) (bytes.drop 4)).mp
      rw [List.take_append_drop, hhead, show (UInt32.ofNat 4 : UInt32) = 4 from rfl] at h
      exact h
    icases happ $$ Hbytes with ⟨Hhead, Htail⟩
    iexists WordCodec.decodeU32 (bytes.take 4)
    iexists WordCodec.decodeU32 (bytes.drop 4)
    isplitl [Hhead]
    · iapply (pointsToBytes_four_as_u32 memId addr _ hhead).mp
      iexact Hhead
    · iapply (pointsToBytes_four_as_u32 memId (addr + 4) _ htail).mp
      iexact Htail
  · iintro ⟨%key, %value, Hkey, Hvalue⟩
    have hforget := slotCell_forget (α := α) memId addr key value
    simp only [slotCell] at hforget ⊢
    iapply hforget
    isplitl [Hkey]
    · iexact Hkey
    · iexact Hvalue

/-- The buckets of two lists in a row. -/
theorem slotsBefore_append (memId : Nat) (ctrl : UInt32)
    (xs ys : List (Option (UInt32 × UInt32))) :
    slotsBefore (α := α) memId ctrl (xs ++ ys) ⊣⊢
      iprop(slotsBefore memId ctrl xs ∗
        slotsBefore memId (ctrl - UInt32.ofNat (8 * xs.length)) ys) := by
  induction xs generalizing ctrl with
  | nil =>
    simp only [List.nil_append, slotsBefore, List.length_nil, Nat.mul_zero]
    rw [show UInt32.ofNat 0 = 0 from rfl, UInt32.sub_zero]
    exact BI.emp_sep.symm
  | cons slot rest ih =>
    simp only [List.cons_append, slotsBefore, List.length_cons]
    have haddr : ctrl - 8 - UInt32.ofNat (8 * rest.length) =
        ctrl - UInt32.ofNat (8 * (rest.length + 1)) := by
      rw [sub_sub_addr, Nat.mul_succ, UInt32.ofNat_add, UInt32.add_comm]
      rfl
    rw [← haddr]
    exact (BI.sep_congr .rfl (ih (ctrl - 8))).trans BI.sep_assoc.symm

/-- Bucket `i` alone, with the buckets before and after it. -/
theorem slotsBefore_focus (memId : Nat) (ctrl : UInt32)
    (slots : List (Option (UInt32 × UInt32))) {i : Nat} (hi : i < slots.length) :
    slotsBefore (α := α) memId ctrl slots ⊣⊢
      iprop(slotsBefore memId ctrl (slots.take i) ∗
        slotCell memId (bucketAddr ctrl i) slots[i] ∗
        slotsBefore memId (bucketAddr ctrl i) (slots.drop (i + 1))) := by
  have hsplit : slots = slots.take i ++ (slots[i] :: slots.drop (i + 1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hprefix : (slots.take i).length = i := by rw [List.length_take]; omega
  have haddr : ctrl - UInt32.ofNat (8 * i) - 8 = bucketAddr ctrl i := by
    rw [bucketAddr, sub_sub_addr, Nat.mul_succ, UInt32.ofNat_add]
    rfl
  conv_lhs => rw [hsplit]
  refine (slotsBefore_append memId ctrl _ _).trans ?_
  rw [hprefix]
  simp only [slotsBefore, haddr]
  exact .rfl

/-- Bucket `i` after `slots.set i slot`: the same prefix and suffix, and the
new pair in the middle. -/
theorem slotsBefore_set (memId : Nat) (ctrl : UInt32)
    (slots : List (Option (UInt32 × UInt32))) {i : Nat} (hi : i < slots.length)
    (slot : Option (UInt32 × UInt32)) :
    slotsBefore (α := α) memId ctrl (slots.set i slot) ⊣⊢
      iprop(slotsBefore memId ctrl (slots.take i) ∗
        slotCell memId (bucketAddr ctrl i) slot ∗
        slotsBefore memId (bucketAddr ctrl i) (slots.drop (i + 1))) := by
  have hi' : i < (slots.set i slot).length := by rw [List.length_set]; exact hi
  refine (slotsBefore_focus memId ctrl _ hi').trans ?_
  rw [List.getElem_set_self, List.take_set_of_le (Nat.le_refl i),
    List.drop_set_of_lt (Nat.lt_succ_self i)]
  exact .rfl

/-! ## The table -/

/-- The four words of `RawTableInner` at `base`. -/
def tableHeader (memId : Nat) (base ctrl mask growthLeft items : UInt32) :
    IProp (WasmHeapGF α) :=
  iprop(pointsTo_u32 memId base ctrl ∗ pointsTo_u32 memId (base + 4) mask ∗
    pointsTo_u32 memId (base + 8) growthLeft ∗ pointsTo_u32 memId (base + 12) items)

/-- An allocated table: the header at `base`, the control bytes at `ctrl`
and every bucket below `ctrl`.  The bound keeps the bucket addresses from
a wrap. -/
def TableBody (memId : Nat) (base ctrl : UInt32) (t : Table UInt32 UInt32) :
    IProp (WasmHeapGF α) :=
  iprop(⌜8 * t.buckets ≤ ctrl.toNat⌝ ∗
    tableHeader memId base ctrl (UInt32.ofNat (t.buckets - 1))
      (UInt32.ofNat t.growthLeft) (UInt32.ofNat t.items) ∗
    Slices.ByteSlice memId ctrl t.ctrl ∗
    slotsBefore memId ctrl t.slots)

/-- The singleton table of `RawTableInner::NEW`: `bucket_mask` is zero,
`ctrl` points at the static empty group, and no bucket is allocated.
The static singleton owns one group of eight `EMPTY` bytes.  The model
keeps nine control bytes (`Table.empty.ctrl.length = 9`), because an
allocated table of one bucket mirrors its bucket byte.  That ninth byte
has no physical home in the static segment, so the conjunct here claims
the first eight bytes only. -/
def SingletonBody (memId : Nat) (base ctrl : UInt32) (t : Table UInt32 UInt32) :
    IProp (WasmHeapGF α) :=
  iprop(⌜t.buckets = 1 ∧ t.items = 0 ∧ t.growthLeft = 0⌝ ∗
    tableHeader memId base ctrl 0 0 0 ∗
    Slices.ByteSlice memId ctrl (t.ctrl.take 8))

/-- A table at `base`, in either of its two physical forms. -/
def TableAt (memId : Nat) (base : UInt32) (t : Table UInt32 UInt32) :
    IProp (WasmHeapGF α) :=
  iprop(∃ ctrl : UInt32,
    SingletonBody memId base ctrl t ∨ (⌜1 < t.buckets⌝ ∗ TableBody memId base ctrl t))

/-- The group at a probe position of an allocated well-formed table, as
one owned `u64`, with the header and the buckets framed. -/
theorem TableBody_groupAt {hash : UInt32 → UInt64} (memId : Nat) (base ctrl : UInt32)
    (t : Table UInt32 UInt32) (hw : Layout hash t) {pos : Nat} (hpos : pos < t.buckets) :
    TableBody (α := α) memId base ctrl t ⊣⊢
      iprop(⌜8 * t.buckets ≤ ctrl.toNat⌝ ∗
        tableHeader memId base ctrl (UInt32.ofNat (t.buckets - 1))
          (UInt32.ofNat t.growthLeft) (UInt32.ofNat t.items) ∗
        (Slices.ByteSlice memId ctrl (t.ctrl.take pos) ∗
          (⌜(ctrl + UInt32.ofNat pos).toNat + 8 < UInt32.size⌝ ∗
            pointsTo_u64 memId (ctrl + UInt32.ofNat pos) (groupWord (groupAt t pos))) ∗
          Slices.ByteSlice memId (ctrl + UInt32.ofNat (pos + 8)) (t.ctrl.drop (pos + 8))) ∗
        slotsBefore memId ctrl t.slots) := by
  unfold TableBody
  refine BI.sep_congr .rfl (BI.sep_congr .rfl (BI.sep_congr ?_ .rfl))
  exact ByteSlice_groupAt memId ctrl t (by rw [hw.ctrl_len]; omega)

/-- Bucket `i` of an allocated well-formed table, with everything else
framed. -/
theorem TableBody_slot {hash : UInt32 → UInt64} (memId : Nat) (base ctrl : UInt32)
    (t : Table UInt32 UInt32) (hw : Layout hash t) {i : Nat} (hi : i < t.buckets) :
    TableBody (α := α) memId base ctrl t ⊣⊢
      iprop(⌜8 * t.buckets ≤ ctrl.toNat⌝ ∗
        tableHeader memId base ctrl (UInt32.ofNat (t.buckets - 1))
          (UInt32.ofNat t.growthLeft) (UInt32.ofNat t.items) ∗
        Slices.ByteSlice memId ctrl t.ctrl ∗
        (slotsBefore memId ctrl (t.slots.take i) ∗
          slotCell memId (bucketAddr ctrl i) (slotAt t i) ∗
          slotsBefore memId (bucketAddr ctrl i) (t.slots.drop (i + 1)))) := by
  unfold TableBody
  have hi' : i < t.slots.length := by rw [hw.slots_len]; exact hi
  refine BI.sep_congr .rfl (BI.sep_congr .rfl (BI.sep_congr .rfl ?_))
  refine (slotsBefore_focus memId ctrl t.slots hi').trans ?_
  rw [slotAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
  exact .rfl

/-- The bucket address of the model, for an index below `buckets`, has no
wrap: it is `ctrl - 8 * (i + 1)` as a number. -/
theorem bucketAddr_toNat (ctrl : UInt32) {buckets i : Nat} (hi : i < buckets)
    (hroom : 8 * buckets ≤ ctrl.toNat) :
    (bucketAddr ctrl i).toNat = ctrl.toNat - 8 * (i + 1) := by
  have hlt : 8 * (i + 1) < UInt32.size := by
    have := UInt32.toNat_lt ctrl
    simp only [UInt32.size] at this ⊢
    omega
  rw [bucketAddr, UInt32.toNat_sub_of_le]
  · rw [UInt32.toNat_ofNat_of_lt' hlt]
  · rw [UInt32.le_iff_toNat_le, UInt32.toNat_ofNat_of_lt' hlt]
    omega

end Ownership

end Wasm.RustStd.HashMap.Table
