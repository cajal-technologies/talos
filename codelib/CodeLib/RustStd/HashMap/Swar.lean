import CodeLib.RustStd.HashMap.TableRefinement
import CodeLib.RustStd.HashMap.SipHash

/-!
# The SWAR group formulas of `hashbrown` against the per-byte predicates

`CodeLib.RustStd.HashMap.Table` reads a group as a list of eight control
bytes and tests each byte on its own.  The compiled program reads the same
eight bytes as one `u64` and tests all of them at once with the three
formulas of `src/control/group/generic.rs` in `hashbrown` 0.16.1:

* `match_empty_or_deleted`: `x & repeat(0x80)`;
* `match_empty`: `x & (x << 1) & repeat(0x80)`;
* `match_tag(tag)`: `cmp = x ^ repeat(tag)`, then
  `(cmp - repeat(0x01)) & !cmp & repeat(0x80)`.

On wasm32 the generic group is a `u64` in little-endian order, `to_le` is
the identity, and `repeat(t)` is `u64::from_ne_bytes([t; 8])`.  A result
bit mask holds one flag per byte at bit 7 of that byte (`BITMASK_STRIDE`
is 8), `lowest_set_bit` is `trailing_zeros / 8`, and `BitMaskIter` yields
the set bytes in ascending order.  This file defines those operations as
pure functions on `UInt64` and proves them against the predicates of
`Table`, for a group word packed by `SipHash.u64OfBytesLE`, the
little-endian packer the SipHash model already uses.

The results, for a group `g` of eight bytes and its word `x`:

* `match_empty_or_deleted` is exact: byte `j` is flagged if and only if
  `isSpecial (g[j])`, and the lowest flagged byte is `lowestSpecial g`.
* `match_empty` is exact on control bytes.  A control byte is `0xFF`,
  `0x80` or below `0x80` (`IsCtrl`), and bit 7 of `x & (x << 1)` in byte
  `j` is bits 7 and 6 of that byte, which among control bytes only `0xFF`
  sets.  Then the flag is `isEmpty (g[j])`, the mask is zero if and only
  if `matchEmpty g = false`, and its trailing and leading clear bytes are
  `trailNonEmpty g` and `leadNonEmpty g`.
* `match_tag` has false positives.  A byte equal to the tag is flagged.
  A flagged byte is the tag or the tag with bit 0 flipped, and it is a
  full byte when the tag is.  The flagged bytes, in order, contain the
  exact `matchTag tag g` as a sublist.  `Layout.find?_setBytes_eq` closes
  the gap for the loops of `find` and `find_or_find_insert_index`: on a
  table with `Layout`, the first flagged byte whose slot holds the key is
  the first exact match whose slot holds the key, because a false positive
  is a full byte whose tag is not the tag of the key, and `Layout.tag`
  says that the slot under it does not hold the key.
* `Layout.isCtrl_groupAt` discharges `IsCtrl` for every byte of every
  group of a `Clean` table, which is the state of every table the crate
  loads a group from.

Out of scope, left to the memory-level proof: `match_full` and `invert`,
`convert_special_to_empty_and_full_to_deleted` (only `rehash_in_place`
uses it, which the crate cannot reach), the link from the mask functions
to the `i64.ctz` and `i64.clz` instructions of the interpreter, and the
equation between `groupWord` of eight bytes read from memory and the
`i64.load` of the same address.  No proof in this file uses `native_decide`.
-/

namespace Wasm.RustStd.HashMap.Table

/-! ## The word-level operations -/

/-- `repeat(Tag::DELETED)`, also `BitMask::BITMASK_MASK`. -/

def REP80 : UInt64 := 0x8080808080808080

/-- `repeat(Tag(0x01))`, the subtrahend of `match_tag`. -/
def REP01 : UInt64 := 0x0101010101010101

/-- `Group::load`: the eight bytes of a group as one little-endian word. -/
def groupWord (g : List UInt8) : UInt64 := SipHash.u64OfBytesLE g

/-- `repeat(t)`: `u64::from_ne_bytes([t; 8])`. -/
def repeatByte (t : UInt8) : UInt64 := groupWord (List.replicate 8 t)

/-- `Group::match_empty`. -/
def swarMatchEmpty (x : UInt64) : UInt64 := x &&& (x <<< 1) &&& REP80

/-- `Group::match_empty_or_deleted`. -/
def swarMatchEmptyOrDeleted (x : UInt64) : UInt64 := x &&& REP80

/-- `Group::match_tag`, the haszero trick of the generic group. -/
def swarMatchTag (tag : UInt8) (x : UInt64) : UInt64 :=
  let cmp := x ^^^ repeatByte tag
  (cmp - REP01) &&& (~~~cmp) &&& REP80
/-- The flag of byte `j` in a mask: bit `8 * j + 7`. -/
def hasBit (m : UInt64) (j : Nat) : Bool := m.toNat.testBit (8 * j + 7)

/-- The flagged bytes in the order of `BitMaskIter`. -/
def setBytes (m : UInt64) : List Nat := (List.range 8).filter (hasBit m)

/-- `BitMask::lowest_set_bit`, in bytes. -/
def lowestSetByte (m : UInt64) : Option Nat := (List.range 8).find? (hasBit m)

/-- `BitMask::trailing_zeros`, in bytes. -/
def trailingClear (m : UInt64) : Nat := ((List.range 8).takeWhile fun j => !hasBit m j).length

/-- `BitMask::leading_zeros`, in bytes. -/
def leadingClear (m : UInt64) : Nat :=
  ((List.range 8).reverse.takeWhile fun j => !hasBit m j).length
/-- A control byte as `Tag` defines it: `EMPTY`, `DELETED` or a full byte. -/
def IsCtrl (c : UInt8) : Prop := c = EMPTY ∨ c = DELETED ∨ isFull c = true

/-! ## Bytes of a natural number -/

/-- Byte `j` of a natural number, little-endian. -/
def byteOf (n j : Nat) : Nat := n / 2 ^ (8 * j) % 2 ^ 8

/-- The value of a little-endian byte list. -/
def bytesVal : List UInt8 → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 ^ 8 * bytesVal bs

theorem bytesVal_lt : ∀ bs : List UInt8, bytesVal bs < 2 ^ (8 * bs.length)
  | [] => by simp [bytesVal]
  | b :: bs => by
    have ih := bytesVal_lt bs
    have hb := UInt8.toNat_lt b
    simp only [bytesVal, List.length_cons]
    rw [show 8 * (bs.length + 1) = 8 * bs.length + 8 by ring, Nat.pow_add]
    omega

theorem toNat_u64OfBytesLE : ∀ bs : List UInt8, bs.length ≤ 8 →
    (SipHash.u64OfBytesLE bs).toNat = bytesVal bs
  | [], _ => by simp [SipHash.u64OfBytesLE, bytesVal]
  | b :: bs, h => by
    have ih := toNat_u64OfBytesLE bs (by simp at h; omega)
    have hlt := bytesVal_lt bs
    have hb := UInt8.toNat_lt b
    have hlen : 2 ^ (8 * bs.length) ≤ 2 ^ 56 :=
      Nat.pow_le_pow_right (by omega) (by simp at h; omega)
    show ((SipHash.u64OfBytesLE bs <<< 8) ||| b.toUInt64).toNat = b.toNat + 2 ^ 8 * bytesVal bs
    rw [UInt64.toNat_or, UInt64.toNat_shiftLeft, ih, UInt8.toNat_toUInt64,
      show (8 : UInt64).toNat % 64 = 8 by decide, Nat.shiftLeft_eq,
      Nat.mod_eq_of_lt (by omega), Nat.mul_comm (bytesVal bs) (2 ^ 8),
      ← Nat.two_pow_add_eq_or_of_lt hb]
    omega

theorem exists_eight {g : List UInt8} (hg : g.length = 8) :
    ∃ b0 b1 b2 b3 b4 b5 b6 b7, g = [b0, b1, b2, b3, b4, b5, b6, b7] := by
  rcases g with _ | ⟨b0, _ | ⟨b1, _ | ⟨b2, _ | ⟨b3, _ | ⟨b4, _ | ⟨b5, _ | ⟨b6, _ | ⟨b7, _ | ⟨b8, rest⟩⟩⟩⟩⟩⟩⟩⟩⟩
  all_goals simp at hg
  exact ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩

theorem byteOf_and (x y j : Nat) : byteOf (x &&& y) j = byteOf x j &&& byteOf y j := by
  unfold byteOf
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    Nat.testBit_and]
  cases Nat.decLt i 8 <;> simp_all

theorem byteOf_xor (x y j : Nat) : byteOf (x ^^^ y) j = byteOf x j ^^^ byteOf y j := by
  unfold byteOf
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight,
    Nat.testBit_xor]
  cases Nat.decLt i 8 <;> simp_all

theorem byteOf_lt (n j : Nat) : byteOf n j < 256 := Nat.mod_lt _ (by decide)

theorem byteOf_not {x j : Nat} (hx : x < 2 ^ 64) (hj : j < 8) :
    byteOf (2 ^ 64 - 1 - x) j = 255 - byteOf x j := by
  interval_cases j <;> simp only [byteOf, Nat.reduceMul, Nat.reducePow] <;> omega

theorem byteOf_shiftLeft_one {x j : Nat} (hj : j < 8) :
    byteOf ((x <<< 1) % 2 ^ 64) j / 128 % 2 = byteOf x j / 64 % 2 := by
  rw [Nat.shiftLeft_eq]
  interval_cases j <;> simp only [byteOf, Nat.reduceMul, Nat.reducePow] <;> omega

/-- The borrow into byte `j` of `x - REP01`. -/
def borrow (x j : Nat) : Nat := if x % 2 ^ (8 * j) < REP01.toNat % 2 ^ (8 * j) then 1 else 0

theorem byteOf_sub_rep01 {x j : Nat} (_hx : x < 2 ^ 64) (hj : j < 8) :
    byteOf ((2 ^ 64 - REP01.toNat + x) % 2 ^ 64) j = (byteOf x j + 255 - borrow x j) % 256 := by
  have h01 : REP01.toNat = 0x0101010101010101 := by decide
  rw [h01]
  unfold borrow
  rw [h01]
  interval_cases j <;> simp only [byteOf, Nat.reduceMul, Nat.reducePow, Nat.reduceMod] <;>
    split <;> omega

theorem byteOf_zero_of_lt {b v : Nat} (hb : b < 256) : byteOf (b + 2 ^ 8 * v) 0 = b := by
  unfold byteOf
  simp only [Nat.mul_zero, Nat.pow_zero, Nat.div_one]
  omega

theorem byteOf_succ {b v j : Nat} (hb : b < 256) : byteOf (b + 2 ^ 8 * v) (j + 1) = byteOf v j := by
  unfold byteOf
  rw [show 2 ^ (8 * (j + 1)) = 2 ^ 8 * 2 ^ (8 * j) by ring, ← Nat.div_div_eq_div_mul,
    show (b + 2 ^ 8 * v) / 2 ^ 8 = v by omega]

theorem byteOf_bytesVal : ∀ (bs : List UInt8) (j : Nat), j < bs.length →
    byteOf (bytesVal bs) j = (bs.getD j EMPTY).toNat
  | [], j, hj => by simp at hj
  | b :: bs, 0, _ => by
    simp only [bytesVal, List.getD_cons_zero]
    exact byteOf_zero_of_lt (UInt8.toNat_lt b)
  | b :: bs, j + 1, hj => by
    simp only [bytesVal, List.getD_cons_succ]
    rw [byteOf_succ (UInt8.toNat_lt b)]
    exact byteOf_bytesVal bs j (by simp at hj; omega)

theorem byteOf_groupWord {g : List UInt8} (hg : g.length = 8) {j : Nat} (hj : j < 8) :
    byteOf (groupWord g).toNat j = (g.getD j EMPTY).toNat := by
  rw [groupWord, toNat_u64OfBytesLE _ (by omega), byteOf_bytesVal _ _ (by omega)]

theorem byteOf_repeatByte (t : UInt8) {j : Nat} (hj : j < 8) :
    byteOf (repeatByte t).toNat j = t.toNat := by
  rw [repeatByte, byteOf_groupWord (by simp) hj]
  interval_cases j <;> rfl

theorem byteOf_REP80 {j : Nat} (hj : j < 8) : byteOf REP80.toNat j = 128 := by
  have h : REP80.toNat = 0x8080808080808080 := by decide
  rw [h]
  interval_cases j <;> decide

theorem hasBit_eq (m : UInt64) {j : Nat} (hj : j < 8) :
    hasBit m j = decide (128 ≤ byteOf m.toNat j) := by
  unfold hasBit byteOf
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have hm := UInt64.toNat_lt m
  interval_cases j <;> simp only [Nat.reduceMul, Nat.reducePow, Nat.reduceAdd] <;>
    (congr 1; apply propext; omega)


/-! ## Bits of bytes and flags of words -/

theorem testBit_byteOf (x j i : Nat) :
    (byteOf x j).testBit i = (decide (i < 8) && x.testBit (8 * j + i)) := by
  unfold byteOf
  rw [Nat.testBit_mod_two_pow, ← Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]

theorem testBit_seven_eq {n : Nat} (hn : n < 256) : n.testBit 7 = decide (128 ≤ n) := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  congr 1
  apply propext
  omega

theorem hasBit_and (a b : UInt64) (j : Nat) : hasBit (a &&& b) j = (hasBit a j && hasBit b j) := by
  unfold hasBit
  rw [UInt64.toNat_and, Nat.testBit_and]

theorem hasBit_REP80 {j : Nat} (hj : j < 8) : hasBit REP80 j = true := by
  unfold hasBit
  interval_cases j <;> decide

theorem hasBit_shiftLeft_one (x : UInt64) {j : Nat} (hj : j < 8) :
    hasBit (x <<< 1) j = x.toNat.testBit (8 * j + 6) := by
  unfold hasBit
  rw [UInt64.toNat_shiftLeft, Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft]
  have h1 : (1 : UInt64).toNat % 64 = 1 := by decide
  rw [h1]
  interval_cases j <;> rfl

theorem testBit_groupWord {g : List UInt8} (hg : g.length = 8) {j : Nat} (hj : j < 8)
    {i : Nat} (hi : i < 8) :
    (groupWord g).toNat.testBit (8 * j + i) = (g.getD j EMPTY).toNat.testBit i := by
  have h := testBit_byteOf (groupWord g).toNat j i
  rw [byteOf_groupWord hg hj, decide_eq_true hi, Bool.true_and] at h
  exact h.symm

theorem hasBit_groupWord {g : List UInt8} (hg : g.length = 8) {j : Nat} (hj : j < 8) :
    hasBit (groupWord g) j = (g.getD j EMPTY).toNat.testBit 7 :=
  testBit_groupWord hg hj (by decide)

theorem eq_zero_iff_hasBit (a : UInt64) :
    a &&& REP80 = 0 ↔ ∀ j < 8, hasBit (a &&& REP80) j = false := by
  constructor
  · intro h j _
    rw [h]
    unfold hasBit
    rw [UInt64.toNat_zero, Nat.zero_testBit]
  · intro h
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_zero]
    have hlt := UInt64.toNat_lt (a &&& REP80)
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    have h2 := h 2 (by decide)
    have h3 := h 3 (by decide)
    have h4 := h 4 (by decide)
    have h5 := h 5 (by decide)
    have h6 := h 6 (by decide)
    have h7 := h 7 (by decide)
    simp only [hasBit_eq _ (by decide : (0:Nat) < 8), hasBit_eq _ (by decide : (1:Nat) < 8),
      hasBit_eq _ (by decide : (2:Nat) < 8), hasBit_eq _ (by decide : (3:Nat) < 8),
      hasBit_eq _ (by decide : (4:Nat) < 8), hasBit_eq _ (by decide : (5:Nat) < 8),
      hasBit_eq _ (by decide : (6:Nat) < 8), hasBit_eq _ (by decide : (7:Nat) < 8),
      decide_eq_false_iff_not, Nat.not_le] at h0 h1 h2 h3 h4 h5 h6 h7
    have hm : ∀ j < 8, byteOf (a &&& REP80).toNat j = byteOf a.toNat j &&& 128 := by
      intro j hj
      rw [UInt64.toNat_and, byteOf_and, byteOf_REP80 hj]
    have hb : ∀ b < 256, b &&& 128 = if 128 ≤ b then 128 else 0 := by decide +kernel
    have hz : ∀ j < 8, byteOf (a &&& REP80).toNat j = 0 := by
      intro j hj
      have := h j hj
      rw [hasBit_eq _ hj, decide_eq_false_iff_not, Nat.not_le, hm j hj,
        hb _ (byteOf_lt _ _)] at this
      rw [hm j hj, hb _ (byteOf_lt _ _)]
      split at this <;> split <;> omega
    have e0 := hz 0 (by decide)
    have e1 := hz 1 (by decide)
    have e2 := hz 2 (by decide)
    have e3 := hz 3 (by decide)
    have e4 := hz 4 (by decide)
    have e5 := hz 5 (by decide)
    have e6 := hz 6 (by decide)
    have e7 := hz 7 (by decide)
    simp only [byteOf, Nat.reduceMul, Nat.reducePow, Nat.mul_zero, Nat.pow_zero,
      Nat.div_one] at e0 e1 e2 e3 e4 e5 e6 e7
    omega

/-! ## Lists indexed by `List.range 8` -/

theorem find?_range'_eq_findIdx? {α : Type} {q : α → Bool} (p : Nat → Bool) (d : α) :
    ∀ (l : List α) (i : Nat), (∀ j < l.length, p (i + j) = q (l.getD j d)) →
      (List.range' i l.length).find? p = (l.findIdx? q).map (fun k => k + i)
  | [], i, _ => by simp
  | a :: l, i, h => by
    rw [List.length_cons, List.range'_succ, List.find?_cons, List.findIdx?_cons]
    have h0 := h 0 (Nat.succ_pos _)
    simp only [Nat.add_zero, List.getD_cons_zero] at h0
    rw [h0]
    have ih := find?_range'_eq_findIdx? p d l (i + 1) (fun j hj => by
      have := h (j + 1) (by simp only [List.length_cons]; omega)
      rw [List.getD_cons_succ] at this
      rw [Nat.add_right_comm]
      exact this)
    cases q a
    · simp only [Bool.false_eq_true, ↓reduceIte, ih, Option.map_map]
      congr 1
      funext k
      simp only [Function.comp]
      omega
    · simp

theorem length_takeWhile_forall₂ {α β : Type} {p : α → Bool} {q : β → Bool} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ (fun a b => p a = q b) l₁ l₂ →
      (l₁.takeWhile p).length = (l₂.takeWhile q).length
  | _, _, .nil => rfl
  | _, _, .cons h hs => by
    rw [List.takeWhile_cons, List.takeWhile_cons, h]
    split
    · simp only [List.length_cons, length_takeWhile_forall₂ hs]
    · rfl

theorem forall₂_range8 {R : Nat → UInt8 → Prop} {g : List UInt8} (hg : g.length = 8)
    (h : ∀ j < 8, R j (g.getD j EMPTY)) : List.Forall₂ R (List.range 8) g := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_eight hg
  simp only [show List.range 8 = [0, 1, 2, 3, 4, 5, 6, 7] from rfl, List.forall₂_cons]
  exact ⟨h 0 (by decide), h 1 (by decide), h 2 (by decide), h 3 (by decide), h 4 (by decide),
    h 5 (by decide), h 6 (by decide), h 7 (by decide), List.Forall₂.nil⟩

theorem forall₂_range8_reverse {R : Nat → UInt8 → Prop} {g : List UInt8} (hg : g.length = 8)
    (h : ∀ j < 8, R j (g.getD j EMPTY)) :
    List.Forall₂ R (List.range 8).reverse g.reverse := by
  obtain ⟨b0, b1, b2, b3, b4, b5, b6, b7, rfl⟩ := exists_eight hg
  simp only [show (List.range 8).reverse = [7, 6, 5, 4, 3, 2, 1, 0] from rfl,
    show [b0, b1, b2, b3, b4, b5, b6, b7].reverse = [b7, b6, b5, b4, b3, b2, b1, b0] from rfl,
    List.forall₂_cons]
  exact ⟨h 7 (by decide), h 6 (by decide), h 5 (by decide), h 4 (by decide), h 3 (by decide),
    h 2 (by decide), h 1 (by decide), h 0 (by decide), List.Forall₂.nil⟩

/-! ## `match_empty_or_deleted` -/

theorem hasBit_swarMatchEmptyOrDeleted {g : List UInt8} (hg : g.length = 8) {j : Nat}
    (hj : j < 8) :
    hasBit (swarMatchEmptyOrDeleted (groupWord g)) j = isSpecial (g.getD j EMPTY) := by
  unfold swarMatchEmptyOrDeleted
  rw [hasBit_and, hasBit_REP80 hj, Bool.and_true, hasBit_groupWord hg hj,
    testBit_seven_eq (UInt8.toNat_lt _)]
  unfold isSpecial
  simp only [UInt8.le_iff_toNat_le]
  rfl

theorem lowestSetByte_swarMatchEmptyOrDeleted {g : List UInt8} (hg : g.length = 8) :
    lowestSetByte (swarMatchEmptyOrDeleted (groupWord g)) = lowestSpecial g := by
  unfold lowestSetByte lowestSpecial
  rw [← hg, List.range_eq_range',
    find?_range'_eq_findIdx? _ EMPTY g 0 (fun j hj => by
      rw [Nat.zero_add]
      exact hasBit_swarMatchEmptyOrDeleted hg (by omega))]
  simp

/-! ## `match_empty` on control bytes -/

theorem hasBit_swarMatchEmpty {g : List UInt8} (hg : g.length = 8) {j : Nat} (hj : j < 8)
    (hc : IsCtrl (g.getD j EMPTY)) :
    hasBit (swarMatchEmpty (groupWord g)) j = isEmpty (g.getD j EMPTY) := by
  unfold swarMatchEmpty
  rw [hasBit_and, hasBit_and, hasBit_REP80 hj, Bool.and_true, hasBit_groupWord hg hj,
    hasBit_shiftLeft_one _ hj, testBit_groupWord hg hj (by decide)]
  rcases hc with hc | hc | hc
  · rw [hc]; decide
  · rw [hc]; decide
  · have hlt : (g.getD j EMPTY).toNat < 128 := by
      unfold isFull at hc
      simpa [UInt8.lt_iff_toNat_lt] using hc
    rw [testBit_seven_eq (UInt8.toNat_lt _), decide_eq_false (by omega), Bool.false_and]
    have hne : g.getD j EMPTY ≠ EMPTY := by
      intro h
      rw [h] at hlt
      exact absurd hlt (by decide)
    unfold isEmpty
    exact (beq_eq_false_iff_ne.mpr hne).symm

theorem getD_mem {g : List UInt8} {j : Nat} (hj : j < g.length) : g.getD j EMPTY ∈ g := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  exact List.getElem_mem hj

theorem mem_iff_getD {g : List UInt8} {c : UInt8} :
    c ∈ g ↔ ∃ j < g.length, g.getD j EMPTY = c := by
  rw [List.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, hj, by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]⟩

theorem swarMatchEmpty_eq_zero_iff {g : List UInt8} (hg : g.length = 8)
    (hc : ∀ c ∈ g, IsCtrl c) :
    swarMatchEmpty (groupWord g) = 0 ↔ matchEmpty g = false := by
  have hall : ∀ j < 8, hasBit (swarMatchEmpty (groupWord g)) j = isEmpty (g.getD j EMPTY) :=
    fun j hj => hasBit_swarMatchEmpty hg hj (hc _ (getD_mem (by omega)))
  unfold matchEmpty
  rw [List.any_eq_false]
  show (groupWord g &&& (groupWord g <<< 1)) &&& REP80 = 0 ↔ _
  rw [eq_zero_iff_hasBit]
  constructor
  · intro h c hcg
    obtain ⟨j, hj, rfl⟩ := mem_iff_getD.mp hcg
    have this : hasBit (swarMatchEmpty (groupWord g)) j = false := h j (by omega)
    rw [← hall j (by omega), this]
    exact Bool.false_ne_true
  · intro h j hj
    have := hall j hj
    show hasBit (swarMatchEmpty (groupWord g)) j = false
    rw [this]
    exact Bool.eq_false_iff.mpr (h _ (getD_mem (by omega)))

theorem trailingClear_swarMatchEmpty {g : List UInt8} (hg : g.length = 8)
    (hc : ∀ c ∈ g, IsCtrl c) :
    trailingClear (swarMatchEmpty (groupWord g)) = trailNonEmpty g := by
  unfold trailingClear trailNonEmpty
  exact length_takeWhile_forall₂ (forall₂_range8 hg fun j hj => by
    show (!hasBit (swarMatchEmpty (groupWord g)) j) = (!isEmpty (g.getD j EMPTY))
    rw [hasBit_swarMatchEmpty hg hj (hc _ (getD_mem (by omega)))])

theorem leadingClear_swarMatchEmpty {g : List UInt8} (hg : g.length = 8)
    (hc : ∀ c ∈ g, IsCtrl c) :
    leadingClear (swarMatchEmpty (groupWord g)) = leadNonEmpty g := by
  unfold leadingClear leadNonEmpty
  exact length_takeWhile_forall₂ (forall₂_range8_reverse hg fun j hj => by
    show (!hasBit (swarMatchEmpty (groupWord g)) j) = (!isEmpty (g.getD j EMPTY))
    rw [hasBit_swarMatchEmpty hg hj (hc _ (getD_mem (by omega)))])

/-! ## `match_tag` -/

theorem borrow_le_one (x j : Nat) : borrow x j ≤ 1 := by
  unfold borrow
  split <;> omega

theorem byteOf_cmp {g : List UInt8} (hg : g.length = 8) (tag : UInt8) {j : Nat} (hj : j < 8) :
    byteOf (groupWord g ^^^ repeatByte tag).toNat j = (g.getD j EMPTY).toNat ^^^ tag.toNat := by
  rw [UInt64.toNat_xor, byteOf_xor, byteOf_groupWord hg hj, byteOf_repeatByte tag hj]

theorem hasBit_swarMatchTag_iff (tag : UInt8) (x : UInt64) {j : Nat} (hj : j < 8) :
    hasBit (swarMatchTag tag x) j = true ↔
      128 ≤ (byteOf (x ^^^ repeatByte tag).toNat j + 255 -
        borrow (x ^^^ repeatByte tag).toNat j) % 256 ∧
      byteOf (x ^^^ repeatByte tag).toNat j < 128 := by
  simp only [swarMatchTag]
  rw [hasBit_and, hasBit_and, hasBit_REP80 hj, Bool.and_true, hasBit_eq _ hj, hasBit_eq _ hj,
    UInt64.toNat_sub, byteOf_sub_rep01 (UInt64.toNat_lt _) hj, UInt64.toNat_not,
    show UInt64.size = 2 ^ 64 from rfl, byteOf_not (UInt64.toNat_lt _) hj, Bool.and_eq_true,
    decide_eq_true_iff, decide_eq_true_iff]
  have hb := byteOf_lt (x ^^^ repeatByte tag).toNat j
  omega

theorem hasBit_swarMatchTag_of_eq {g : List UInt8} (hg : g.length = 8) {j : Nat} (hj : j < 8)
    (tag : UInt8) (h : g.getD j EMPTY = tag) :
    hasBit (swarMatchTag tag (groupWord g)) j = true := by
  rw [hasBit_swarMatchTag_iff _ _ hj, byteOf_cmp hg tag hj, h, Nat.xor_self]
  have := borrow_le_one (groupWord g ^^^ repeatByte tag).toNat j
  omega

theorem eq_or_eq_of_hasBit_swarMatchTag {g : List UInt8} (hg : g.length = 8) {j : Nat}
    (hj : j < 8) {tag : UInt8} (h : hasBit (swarMatchTag tag (groupWord g)) j = true) :
    g.getD j EMPTY = tag ∨ g.getD j EMPTY = tag ^^^ 1 := by
  rw [hasBit_swarMatchTag_iff _ _ hj, byteOf_cmp hg tag hj] at h
  have hb := borrow_le_one (groupWord g ^^^ repeatByte tag).toNat j
  have hd : (g.getD j EMPTY).toNat ^^^ tag.toNat = 0 ∨
      (g.getD j EMPTY).toNat ^^^ tag.toNat = 1 := by omega
  rcases hd with hd | hd
  · left
    apply UInt8.toNat_inj.mp
    have := congrArg (· ^^^ tag.toNat) hd
    simpa only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero, Nat.zero_xor] using this
  · right
    apply UInt8.toNat_inj.mp
    rw [UInt8.toNat_xor, UInt8.toNat_one]
    have := congrArg (· ^^^ tag.toNat) hd
    simp only [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero] at this
    rw [this, Nat.xor_comm]

theorem isFull_of_hasBit_swarMatchTag {g : List UInt8} (hg : g.length = 8) {j : Nat}
    (hj : j < 8) {tag : UInt8} (htag : isFull tag = true)
    (h : hasBit (swarMatchTag tag (groupWord g)) j = true) :
    isFull (g.getD j EMPTY) = true := by
  rcases eq_or_eq_of_hasBit_swarMatchTag hg hj h with h | h
  · rw [h]; exact htag
  · rw [h]
    unfold isFull at htag ⊢
    rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt, UInt8.toNat_xor, UInt8.toNat_one] at *
    exact Nat.xor_lt_two_pow (n := 7) htag (by decide)

/-! ## The order of the flagged bytes, and the loops -/

theorem matchTag_sublist_setBytes {g : List UInt8} (hg : g.length = 8) (tag : UInt8) :
    (matchTag tag g).Sublist (setBytes (swarMatchTag tag (groupWord g))) := by
  unfold matchTag setBytes
  rw [hg]
  have : (List.range 8).filter (fun j => g.getD j EMPTY == tag) =
      ((List.range 8).filter (hasBit (swarMatchTag tag (groupWord g)))).filter
        (fun j => g.getD j EMPTY == tag) := by
    rw [List.filter_filter]
    apply List.filter_congr
    intro j hj
    rw [List.mem_range] at hj
    cases h : (g.getD j EMPTY == tag)
    · simp
    · rw [hasBit_swarMatchTag_of_eq hg hj tag (beq_iff_eq.mp h)]
      rfl
  rw [this]
  exact List.filter_sublist

theorem mem_setBytes_swarMatchTag {g : List UInt8} (hg : g.length = 8) {tag : UInt8} {j : Nat}
    (h : j ∈ setBytes (swarMatchTag tag (groupWord g))) :
    j < 8 ∧ (g.getD j EMPTY = tag ∨ g.getD j EMPTY = tag ^^^ 1) := by
  unfold setBytes at h
  rw [List.mem_filter, List.mem_range] at h
  exact ⟨h.1, eq_or_eq_of_hasBit_swarMatchTag hg h.1 h.2⟩

theorem find?_filter_eq {α : Type} {p r q : α → Bool} : ∀ (l : List α),
    (∀ a ∈ l, r a = true → p a = true) →
    (∀ a ∈ l, p a = true → r a = false → q a = false) →
    (l.filter p).find? q = (l.filter r).find? q
  | [], _, _ => rfl
  | a :: l, h1, h2 => by
    have ih := find?_filter_eq l (fun x hx => h1 x (List.mem_cons_of_mem _ hx))
      (fun x hx => h2 x (List.mem_cons_of_mem _ hx))
    simp only [List.filter_cons]
    cases hp : p a <;> cases hr : r a
    · simpa using ih
    · exact absurd (h1 a List.mem_cons_self hr) (by simp [hp])
    · have hq := h2 a List.mem_cons_self hp hr
      simp only [List.find?_cons, hq, Bool.false_eq_true, ↓reduceIte]
      exact ih
    · simp only [List.find?_cons, ↓reduceIte]
      cases q a
      · exact ih
      · rfl

theorem xor_one_ne (tag : UInt8) : tag ^^^ 1 ≠ tag := by
  intro h
  have := congrArg UInt8.toNat h
  rw [UInt8.toNat_xor, UInt8.toNat_one] at this
  have h2 := congrArg (tag.toNat ^^^ ·) this
  simp only [← Nat.xor_assoc, Nat.xor_self, Nat.zero_xor] at h2
  exact absurd h2 (by decide)

section Tables

/-! ## Tables with `Layout` -/

variable {K V : Type} {hash : K → UInt64} {t : Table K V}

theorem Layout.keyIs_eq_false_of_ctrl_ne [BEq K] [LawfulBEq K] (hw : Layout hash t) {i : Nat}
    (hi : i < t.buckets)
    {k : K} (hne : t.ctrlAt i ≠ h2 (hash k)) : t.keyIs i k = false := by
  cases h : t.keyIs i k
  · rfl
  · obtain ⟨v, hv⟩ := (keyIs_iff t i k).mp h
    exact absurd (hw.tag i hi k v hv) hne

theorem Layout.find?_setBytes_eq [BEq K] [LawfulBEq K] (hw : Layout hash t) {p : Nat}
    (hp : p < t.buckets) (k : K) :
    (setBytes (swarMatchTag (h2 (hash k)) (groupWord (groupAt t p)))).find?
        (fun j => t.keyIs ((p + j) % t.buckets) k) =
      (matchTag (h2 (hash k)) (groupAt t p)).find? (fun j => t.keyIs ((p + j) % t.buckets) k) := by
  unfold setBytes matchTag
  rw [groupAt_length]
  apply find?_filter_eq
  · intro j hj h
    exact hasBit_swarMatchTag_of_eq (groupAt_length t p) (List.mem_range.mp hj) _
      (beq_iff_eq.mp h)
  · intro j hj hb hne
    have hj8 := List.mem_range.mp hj
    rcases eq_or_eq_of_hasBit_swarMatchTag (groupAt_length t p) hj8 hb with h | h
    · rw [h] at hne
      simp at hne
    · rw [groupAt_getD _ _ _ hj8] at h
      have hfull : isFull (t.ctrlAt (p + j)) = true := by
        rw [h]
        unfold isFull
        rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt, UInt8.toNat_xor, UInt8.toNat_one]
        have := isFull_h2 (hash k)
        unfold isFull at this
        rw [decide_eq_true_iff, UInt8.lt_iff_toNat_lt] at this
        exact Nat.xor_lt_two_pow (n := 7) this (by decide)
      have hmir := hw.mirror (p + j) (by omega)
      have hnp : ¬ IsPad t.buckets (p + j) := by
        intro hpad
        rw [if_pos hpad] at hmir
        rw [hmir] at hfull
        exact absurd hfull (by decide)
      rw [if_neg hnp] at hmir
      apply hw.keyIs_eq_false_of_ctrl_ne (Nat.mod_lt _ hw.pos)
      rw [← hmir, h]
      exact xor_one_ne _

theorem Layout.isCtrl_groupAt (hw : Layout hash t) (hcl : Clean t) {p : Nat}
    (hp : p < t.buckets) : ∀ c ∈ groupAt t p, IsCtrl c := by
  intro c hc
  obtain ⟨j, hj, rfl⟩ := mem_groupAt.mp hc
  rw [hw.mirror _ (by omega)]
  split
  · exact Or.inl rfl
  · have hi : (p + j) % t.buckets < t.buckets := Nat.mod_lt _ hw.pos
    by_cases hf : isFull (t.ctrlAt ((p + j) % t.buckets)) = true
    · exact Or.inr (Or.inr hf)
    · exact Or.inl (hcl.1 _ hi (isSpecial_iff.mpr hf))

end Tables

end Wasm.RustStd.HashMap.Table
