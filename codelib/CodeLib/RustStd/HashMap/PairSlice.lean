import CodeLib.RustStd.HashMap.TableMem
import CodeLib.RustStd.HashMap.Codec

/-!
# The pair array of the compiled `collect`

`collect_entries` builds a `Vec<(u32, u32)>` and then reads it back.  On
wasm32 that buffer is a packed array of eight-byte entries: the key in the
first four bytes of an entry, the value in the next four.  The compiled
code touches an entry in three ways.  It moves a whole entry with one
`i64.load` or `i64.store` at `buffer + 8 i`.  It reads or writes the key
with an `i32` access at the same address.  It reads or writes the value
with an `i32` access at `buffer + 8 i + 4`.

`PairSlice` is the ownership of that buffer.  It is a thin definition over
`Slices.ByteSlice`, so a caller that holds the bytes and a caller that
holds the entries hold the same resource.  There is no alignment fact: an
entry access is `align=1` or `align=4`, never eight-aligned, so
`Slices.WordSlice` is the wrong base.

`pairBytes` is the wire format of the entry list.  It is
`Project.RustHashMap.CollectContract.entryCodec.serialize` by `rfl`,
because that codec is the same `pairCodec WordCodec.u32le WordCodec.u32le`.
This module does not import the project, so the equation is a comment and
not a theorem.

The lemmas come in three groups:

* the bytes of an entry list (`pairBytes_length`, `pairBytes_append`);
* focus one entry and put it back, as one `u64` (`PairSlice_focus`) or as
  the key and the value words (`PairSlice_key`, `PairSlice_value`,
  `PairSlice_set_value`);
* the pure model of an exchange (`swapAt` and its lemmas), which the sort
  proofs of the next phase state their invariant with.

The focus lemmas give the resource that `twp_load64`, `twp_store64`,
`twp_load32` and `twp_store32` consume, which is `pointsTo_u64` for a whole
entry and `pointsTo_u32` for a key or a value.
-/

namespace Wasm.RustStd.HashMap.Table

open Wasm.SepLogic Wasm.SepLogic.Slices Iris Std

/-! ## The bytes of an entry list -/

/-- The packed bytes of a `Vec<(u32, u32)>` buffer.  This is
`entryCodec.serialize` of `Project.RustHashMap.CollectContract`, which
names the same codec. -/
def pairBytes (pairs : List (UInt32 × UInt32)) : List UInt8 :=
  (pairCodec WordCodec.u32le WordCodec.u32le).serialize pairs

/-- The eight bytes of one entry, as the `u64` that one `i64.load` reads. -/
def pairWord (p : UInt32 × UInt32) : UInt64 :=
  groupWord (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2)

@[simp] theorem pairBytes_nil : pairBytes [] = [] := rfl

/-- One entry is its key bytes and then its value bytes. -/
theorem pairBytes_single (p : UInt32 × UInt32) :
    pairBytes [p] = WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2 := rfl

theorem pairBytes_cons (p : UInt32 × UInt32)
    (ps : List (UInt32 × UInt32)) :
    pairBytes (p :: ps) =
      (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2) ++ pairBytes ps :=
  rfl

/-- The bytes of two entry lists in a row. -/
theorem pairBytes_append (a b : List (UInt32 × UInt32)) :
    pairBytes (a ++ b) = pairBytes a ++ pairBytes b :=
  WordCodec.serialize_append _ a b

/-- Every entry takes eight bytes. -/
@[simp] theorem pairBytes_length (ps : List (UInt32 × UInt32)) :
    (pairBytes ps).length = 8 * ps.length := by
  rw [pairBytes, WordCodec.serialize_length]
  rfl

/-! ## The entry view of a byte list -/

/-- The entry view of a byte list made of complete eight-byte chunks.  A
trailing partial chunk is dropped.  `pairBytes_decodePairs` asks for an
exact length, so the partial case never describes a live buffer. -/
def decodePairs : List UInt8 → List (UInt32 × UInt32)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      (WordCodec.decodeU32 [b0, b1, b2, b3],
        WordCodec.decodeU32 [b4, b5, b6, b7]) :: decodePairs rest
  | _ => []

/-- Every `8 * count`-byte list is the wire format of its `count`-entry
view. -/
theorem pairBytes_decodePairs (bytes : List UInt8) (count : Nat)
    (hlength : bytes.length = 8 * count) :
    pairBytes (decodePairs bytes) = bytes ∧
      (decodePairs bytes).length = count := by
  induction count generalizing bytes with
  | zero =>
      have hnil : bytes = [] := by simpa using hlength
      subst hnil
      simp [decodePairs]
  | succ count ih =>
      rcases bytes with _ | ⟨b0, bytes⟩
      · simp at hlength
      rcases bytes with _ | ⟨b1, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b2, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b3, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b4, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b5, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b6, bytes⟩
      · simp at hlength; omega
      rcases bytes with _ | ⟨b7, rest⟩
      · simp at hlength; omega
      have hrest : rest.length = 8 * count := by
        simp only [List.length_cons, Nat.mul_succ] at hlength; omega
      have hind := ih rest hrest
      have hstep : decodePairs (b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 ::
          b7 :: rest) =
            (WordCodec.decodeU32 [b0, b1, b2, b3],
              WordCodec.decodeU32 [b4, b5, b6, b7]) :: decodePairs rest :=
        rfl
      refine ⟨?_, ?_⟩
      · rw [hstep, pairBytes_cons, hind.1]
        dsimp only
        rw [encodeU32_decodeU32_of_length [b0, b1, b2, b3] rfl,
          encodeU32_decodeU32_of_length [b4, b5, b6, b7] rfl]
        rfl
      · rw [hstep]
        simp [hind.2]

/-! ## Exchange of two entries -/

/-- Exchange entries `i` and `j`.  An index out of bounds keeps the list
unchanged, because `List.set` does. -/
def swapAt (ps : List (UInt32 × UInt32)) (i j : Nat) :
    List (UInt32 × UInt32) :=
  (ps.set i (ps.getD j (0, 0))).set j (ps.getD i (0, 0))

@[simp] theorem swapAt_length (ps : List (UInt32 × UInt32)) (i j : Nat) :
    (swapAt ps i j).length = ps.length := by
  simp [swapAt]

/-- In bounds an exchange is two `List.set` steps.  The sort proofs state
their invariant with this form. -/
theorem swapAt_eq_set_set (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    swapAt ps i j = (ps.set i ps[j]).set j ps[i] := by
  rw [swapAt, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj]
  rfl

theorem swapAt_getElem?_left (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    (swapAt ps i j)[i]? = ps[j]? := by
  rw [swapAt_eq_set_set ps hi hj]
  simp only [List.getElem?_set, List.length_set]
  split_ifs <;> simp_all

theorem swapAt_getElem?_right (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    (swapAt ps i j)[j]? = ps[i]? := by
  rw [swapAt_eq_set_set ps hi hj]
  simp only [List.getElem?_set, List.length_set]
  split_ifs <;> simp_all

theorem swapAt_getElem?_other (ps : List (UInt32 × UInt32)) {i j k : Nat}
    (hki : k ≠ i) (hkj : k ≠ j) :
    (swapAt ps i j)[k]? = ps[k]? := by
  rw [swapAt]
  simp only [List.getElem?_set, List.length_set]
  split_ifs <;> simp_all

/-- Entry `i` of the exchange is entry `j` of the input. -/
theorem swapAt_get_left (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length)
    (hswap : i < (swapAt ps i j).length) :
    (swapAt ps i j)[i]'hswap = ps[j]'hj := by
  have h := swapAt_getElem?_left ps hi hj
  rw [List.getElem?_eq_getElem hswap, List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

/-- Entry `j` of the exchange is entry `i` of the input. -/
theorem swapAt_get_right (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length)
    (hswap : j < (swapAt ps i j).length) :
    (swapAt ps i j)[j]'hswap = ps[i]'hi := by
  have h := swapAt_getElem?_right ps hi hj
  rw [List.getElem?_eq_getElem hswap, List.getElem?_eq_getElem hi] at h
  exact Option.some.inj h

/-- Every other entry keeps its place. -/
theorem swapAt_get_other (ps : List (UInt32 × UInt32)) {i j k : Nat}
    (hki : k ≠ i) (hkj : k ≠ j) (hk : k < ps.length)
    (hswap : k < (swapAt ps i j).length) :
    (swapAt ps i j)[k]'hswap = ps[k]'hk := by
  have h := swapAt_getElem?_other ps hki hkj
  rw [List.getElem?_eq_getElem hswap, List.getElem?_eq_getElem hk] at h
  exact Option.some.inj h

/-- An exchange keeps the content of the list.  A sort proof carries this
fact from step to step. -/
theorem swapAt_perm (ps : List (UInt32 × UInt32)) {i j : Nat}
    (hi : i < ps.length) (hj : j < ps.length) :
    (swapAt ps i j).Perm ps := by
  rw [List.perm_iff_count]
  intro entry
  rw [swapAt_eq_set_set ps hi hj]
  have hlen : (ps.set i ps[j]).length = ps.length := List.length_set
  rw [List.count_set (hlen ▸ hj), List.count_set hi]
  have hset : ((ps.set i ps[j])[j]'(hlen ▸ hj) == entry) =
      (ps[j] == entry) := by
    congr 1
    simp [List.getElem_set]
  rw [hset]
  have hle : (if ps[i] == entry then 1 else 0) ≤ ps.count entry := by
    split_ifs with h
    · exact List.count_pos_iff.mpr ((beq_iff_eq.mp h) ▸ List.getElem_mem hi)
    · exact Nat.zero_le _
  omega

/-! ## The word of an entry -/

/-- Two entries with the same word are the same entry.  The word holds the
key bytes and then the value bytes, and a `u32` is its four bytes. -/
theorem pairWord_inj {p q : UInt32 × UInt32} (h : pairWord p = pairWord q) :
    p = q := by
  have hgetD : ∀ k : Nat, k < 8 →
      (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2).getD k 0 =
        (WordCodec.encodeU32 q.1 ++ WordCodec.encodeU32 q.2).getD k 0 := by
    intro k hk
    rw [← u64Byte_groupWord
        (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2) rfl k hk,
      ← u64Byte_groupWord
        (WordCodec.encodeU32 q.1 ++ WordCodec.encodeU32 q.2) rfl k hk]
    exact congrArg (fun word => u64Byte word k) h
  have h0 := hgetD 0 (by decide)
  have h1 := hgetD 1 (by decide)
  have h2 := hgetD 2 (by decide)
  have h3 := hgetD 3 (by decide)
  have h4 := hgetD 4 (by decide)
  have h5 := hgetD 5 (by decide)
  have h6 := hgetD 6 (by decide)
  have h7 := hgetD 7 (by decide)
  have hbytes : WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2 =
      WordCodec.encodeU32 q.1 ++ WordCodec.encodeU32 q.2 := by
    simp only [encodeU32_eq_u32Bytes, List.cons_append, List.nil_append,
      List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2 h3 h4 h5 h6 h7 ⊢
    rw [h0, h1, h2, h3, h4, h5, h6, h7]
  obtain ⟨hkey, hvalue⟩ := List.append_inj hbytes rfl
  have hdec : ∀ x : UInt32, WordCodec.decodeU32 (WordCodec.encodeU32 x) = x :=
    WordCodec.u32le.decode_encode
  refine Prod.ext_iff.mpr ⟨?_, ?_⟩
  · rw [← hdec p.1, ← hdec q.1, hkey]
  · rw [← hdec p.2, ← hdec q.2, hvalue]

/-! ## Ownership -/

section Ownership

variable {α : Type} [WasmHeapGS α]

/-- Exclusive ownership of a `Vec<(u32, u32)>` buffer at `v`.  This is the
byte slice of the wire format, and nothing more. -/
def PairSlice (memId : Nat) (v : UInt32)
    (pairs : List (UInt32 × UInt32)) : IProp (WasmHeapGF α) :=
  Slices.ByteSlice memId v (pairBytes pairs)

/-- The buffer is its bytes.  A caller that frees the buffer or copies it
takes this direction. -/
theorem PairSlice_forget (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) :
    PairSlice (α := α) memId v ps ⊣⊢
      Slices.ByteSlice memId v (pairBytes ps) := .rfl

/-- The buffer does not wrap around the address space. -/
theorem PairSlice_nowrap (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) :
    PairSlice (α := α) memId v ps ⊢
      iprop(⌜v.toNat + 8 * ps.length < UInt32.size⌝ ∗
        PairSlice memId v ps) := by
  have hfacts : PairSlice (α := α) memId v ps ⊣⊢
      iprop(⌜v.toNat + 8 * ps.length < UInt32.size⌝ ∗
        pointsToBytes memId v (pairBytes ps)) := by
    unfold PairSlice Slices.ByteSlice
    rw [pairBytes_length]
    exact .rfl
  iintro Hslice
  icases hfacts.mp $$ Hslice with ⟨%hnowrap, Hbytes⟩
  isplitl_pureexact hnowrap
  · iapply hfacts.mpr
    isplitl_pureexact hnowrap
    · iexact Hbytes

/-! ### One entry -/

/-- The eight bytes of one entry are the word that `i64.load` reads. -/
theorem ByteSlice_pair_as_u64 (memId : Nat) (ptr : UInt32)
    (p : UInt32 × UInt32) :
    Slices.ByteSlice (α := α) memId ptr
        (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2) ⊣⊢
      iprop(⌜ptr.toNat + 8 < UInt32.size⌝ ∗
        pointsTo_u64 memId ptr (pairWord p)) :=
  ByteSlice_eight_as_u64 memId ptr _ rfl

/-- The eight bytes of one entry are the key word and the value word. -/
theorem ByteSlice_pair_as_words (memId : Nat) (ptr : UInt32)
    (p : UInt32 × UInt32) :
    Slices.ByteSlice (α := α) memId ptr
        (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2) ⊣⊢
      iprop(⌜ptr.toNat + 8 < UInt32.size⌝ ∗
        (pointsTo_u32 memId ptr p.1 ∗
          pointsTo_u32 memId (ptr + 4) p.2)) := by
  unfold Slices.ByteSlice
  rw [show (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2).length = 8
    from rfl]
  refine BI.sep_congr .rfl ?_
  refine (pointsToBytes_append memId ptr _ _).trans ?_
  rw [show ptr + UInt32.ofNat (WordCodec.encodeU32 p.1).length = ptr + 4
    from rfl, encodeU32_eq_u32Bytes, encodeU32_eq_u32Bytes]
  exact BI.sep_congr (pointsTo_u32_as_bytes memId ptr p.1).symm
    (pointsTo_u32_as_bytes memId (ptr + 4) p.2).symm

/-- The head entry of a buffer, as one word, and the rest of the buffer. -/
theorem PairSlice_cons (memId : Nat) (v : UInt32) (p : UInt32 × UInt32)
    (ps : List (UInt32 × UInt32)) :
    PairSlice (α := α) memId v (p :: ps) ⊣⊢
      iprop((⌜v.toNat + 8 < UInt32.size⌝ ∗
          pointsTo_u64 memId v (pairWord p)) ∗
        PairSlice memId (v + 8) ps) := by
  unfold PairSlice
  rw [pairBytes_cons]
  refine (Slices.ByteSlice_append memId v _ _).trans ?_
  rw [show v + UInt32.ofNat
      (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2).length = v + 8
    from rfl]
  exact BI.sep_congr (ByteSlice_pair_as_u64 memId v p) .rfl

/-- The head entry of a buffer, as a key word and a value word. -/
theorem PairSlice_cons_words (memId : Nat) (v : UInt32)
    (p : UInt32 × UInt32) (ps : List (UInt32 × UInt32)) :
    PairSlice (α := α) memId v (p :: ps) ⊣⊢
      iprop((⌜v.toNat + 8 < UInt32.size⌝ ∗
          (pointsTo_u32 memId v p.1 ∗
            pointsTo_u32 memId (v + 4) p.2)) ∗
        PairSlice memId (v + 8) ps) := by
  unfold PairSlice
  rw [pairBytes_cons]
  refine (Slices.ByteSlice_append memId v _ _).trans ?_
  rw [show v + UInt32.ofNat
      (WordCodec.encodeU32 p.1 ++ WordCodec.encodeU32 p.2).length = v + 8
    from rfl]
  exact BI.sep_congr (ByteSlice_pair_as_words memId v p) .rfl

/-! ### Split and focus -/

/-- Split a buffer at an entry boundary, and join two adjacent buffers. -/
theorem PairSlice_split (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) (n : Nat) (hn : n ≤ ps.length) :
    PairSlice (α := α) memId v ps ⊣⊢
      iprop(PairSlice memId v (ps.take n) ∗
        PairSlice memId (v + UInt32.ofNat (8 * n)) (ps.drop n)) := by
  have hsplit : ps = ps.take n ++ ps.drop n :=
    (List.take_append_drop n ps).symm
  have hlen : (pairBytes (ps.take n)).length = 8 * n := by
    rw [pairBytes_length, List.length_take, Nat.min_eq_left hn]
  unfold PairSlice
  conv_lhs => rw [hsplit]
  rw [pairBytes_append]
  refine (Slices.ByteSlice_append memId v _ _).trans ?_
  rw [hlen]
  exact .rfl

/-- Entry `i` alone, as one word, with the entries before and after it. -/
theorem PairSlice_at (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length) :
    PairSlice (α := α) memId v ps ⊣⊢
      iprop(PairSlice memId v (ps.take i) ∗
        (⌜(v + UInt32.ofNat (8 * i)).toNat + 8 < UInt32.size⌝ ∗
          pointsTo_u64 memId (v + UInt32.ofNat (8 * i)) (pairWord ps[i])) ∗
        PairSlice memId (v + UInt32.ofNat (8 * i) + 8)
          (ps.drop (i + 1))) := by
  refine (PairSlice_split memId v ps i (Nat.le_of_lt hi)).trans ?_
  refine BI.sep_congr .rfl ?_
  rw [List.drop_eq_getElem_cons hi]
  exact PairSlice_cons memId _ ps[i] (ps.drop (i + 1))

/-- Entry `i` alone, as a key word and a value word. -/
theorem PairSlice_at_words (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length) :
    PairSlice (α := α) memId v ps ⊣⊢
      iprop(PairSlice memId v (ps.take i) ∗
        (⌜(v + UInt32.ofNat (8 * i)).toNat + 8 < UInt32.size⌝ ∗
          (pointsTo_u32 memId (v + UInt32.ofNat (8 * i)) ps[i].1 ∗
            pointsTo_u32 memId (v + UInt32.ofNat (8 * i) + 4) ps[i].2)) ∗
        PairSlice memId (v + UInt32.ofNat (8 * i) + 8)
          (ps.drop (i + 1))) := by
  refine (PairSlice_split memId v ps i (Nat.le_of_lt hi)).trans ?_
  refine BI.sep_congr .rfl ?_
  rw [List.drop_eq_getElem_cons hi]
  exact PairSlice_cons_words memId _ ps[i] (ps.drop (i + 1))

/-- Entry `i` after `ps.set i q`: the same entries around it, and the new
word in the middle. -/
theorem PairSlice_set (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length)
    (q : UInt32 × UInt32) :
    PairSlice (α := α) memId v (ps.set i q) ⊣⊢
      iprop(PairSlice memId v (ps.take i) ∗
        (⌜(v + UInt32.ofNat (8 * i)).toNat + 8 < UInt32.size⌝ ∗
          pointsTo_u64 memId (v + UInt32.ofNat (8 * i)) (pairWord q)) ∗
        PairSlice memId (v + UInt32.ofNat (8 * i) + 8)
          (ps.drop (i + 1))) := by
  have hi' : i < (ps.set i q).length := by rw [List.length_set]; exact hi
  refine (PairSlice_at memId v (ps.set i q) hi').trans ?_
  rw [List.getElem_set_self, List.take_set_of_le (Nat.le_refl i),
    List.drop_set_of_lt (Nat.lt_succ_self i)]
  exact .rfl

/-- Entry `i` after `ps.set i (key, value)`, as a key word and a value
word. -/
theorem PairSlice_set_words (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length)
    (key value : UInt32) :
    PairSlice (α := α) memId v (ps.set i (key, value)) ⊣⊢
      iprop(PairSlice memId v (ps.take i) ∗
        (⌜(v + UInt32.ofNat (8 * i)).toNat + 8 < UInt32.size⌝ ∗
          (pointsTo_u32 memId (v + UInt32.ofNat (8 * i)) key ∗
            pointsTo_u32 memId (v + UInt32.ofNat (8 * i) + 4) value)) ∗
        PairSlice memId (v + UInt32.ofNat (8 * i) + 8)
          (ps.drop (i + 1))) := by
  have hi' : i < (ps.set i (key, value)).length := by
    rw [List.length_set]; exact hi
  refine (PairSlice_at_words memId v (ps.set i (key, value)) hi').trans ?_
  rw [List.getElem_set_self, List.take_set_of_le (Nat.le_refl i),
    List.drop_set_of_lt (Nat.lt_succ_self i)]
  exact .rfl

/-- Focus entry `i` for an `i64` load or store.  The continuation takes any
new entry and returns the buffer with that entry in place. -/
theorem PairSlice_focus (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length) :
    PairSlice (α := α) memId v ps ⊢
      iprop(pointsTo_u64 memId (v + UInt32.ofNat (8 * i)) (pairWord ps[i]) ∗
        (∀ q : UInt32 × UInt32,
          pointsTo_u64 memId (v + UInt32.ofNat (8 * i)) (pairWord q) -∗
            PairSlice memId v (ps.set i q))) := by
  iintro Hslice
  icases (PairSlice_at memId v ps hi).mp $$ Hslice with
    ⟨Hpre, ⟨%hnowrap, Hcell⟩, Hpost⟩
  isplitl_exact Hcell
  · iintro %q
    iintro Hnew
    iapply (PairSlice_set memId v ps hi q).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hnew]
      · isplitl_pureexact hnowrap
        · iexact Hnew
      · iexact Hpost

/-- Focus the key of entry `i` for an `i32` load or store.  The
continuation takes any new key and keeps the value. -/
theorem PairSlice_key (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length) :
    PairSlice (α := α) memId v ps ⊢
      iprop(pointsTo_u32 memId (v + UInt32.ofNat (8 * i)) ps[i].1 ∗
        (∀ key : UInt32,
          pointsTo_u32 memId (v + UInt32.ofNat (8 * i)) key -∗
            PairSlice memId v (ps.set i (key, ps[i].2)))) := by
  iintro Hslice
  icases (PairSlice_at_words memId v ps hi).mp $$ Hslice with
    ⟨Hpre, ⟨%hnowrap, Hkey, Hvalue⟩, Hpost⟩
  isplitl_exact Hkey
  · iintro %key
    iintro Hnew
    iapply (PairSlice_set_words memId v ps hi key ps[i].2).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hnew Hvalue]
      · isplitl_pureexact hnowrap
        · isplitl_exact Hnew
          · iexact Hvalue
      · iexact Hpost

/-- Focus the value of entry `i` for an `i32` load or store.  The
continuation takes any new value and keeps the key. -/
theorem PairSlice_value (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length) :
    PairSlice (α := α) memId v ps ⊢
      iprop(pointsTo_u32 memId (v + UInt32.ofNat (8 * i) + 4) ps[i].2 ∗
        (∀ value : UInt32,
          pointsTo_u32 memId (v + UInt32.ofNat (8 * i) + 4) value -∗
            PairSlice memId v (ps.set i (ps[i].1, value)))) := by
  iintro Hslice
  icases (PairSlice_at_words memId v ps hi).mp $$ Hslice with
    ⟨Hpre, ⟨%hnowrap, Hkey, Hvalue⟩, Hpost⟩
  isplitl_exact Hvalue
  · iintro %value
    iintro Hnew
    iapply (PairSlice_set_words memId v ps hi ps[i].1 value).mpr
    isplitl [Hpre]
    · iexact Hpre
    · isplitl [Hkey Hnew]
      · isplitl_pureexact hnowrap
        · isplitl_exact Hkey
          · iexact Hnew
      · iexact Hpost

/-- Focus the value of entry `i` for a store of a known value. -/
theorem PairSlice_set_value (memId : Nat) (v : UInt32)
    (ps : List (UInt32 × UInt32)) {i : Nat} (hi : i < ps.length)
    (value : UInt32) :
    PairSlice (α := α) memId v ps ⊢
      iprop(pointsTo_u32 memId (v + UInt32.ofNat (8 * i) + 4) ps[i].2 ∗
        (pointsTo_u32 memId (v + UInt32.ofNat (8 * i) + 4) value -∗
          PairSlice memId v (ps.set i (ps[i].1, value)))) := by
  iintro Hslice
  icases PairSlice_value memId v ps hi $$ Hslice with ⟨Hold, Hclose⟩
  isplitl_exact Hold
  ispecialize Hclose $$ %value
  iexact Hclose

/-- Read a buffer of `8 * n` bytes as a buffer of `n` entries. -/
theorem PairSlice_of_ByteSlice (memId : Nat) (v : UInt32)
    (bytes : List UInt8) (n : Nat) (hlength : bytes.length = 8 * n) :
    Slices.ByteSlice (α := α) memId v bytes ⊢
      iprop(∃ ps : List (UInt32 × UInt32), ⌜ps.length = n⌝ ∗
        PairSlice memId v ps) := by
  have hdecode := pairBytes_decodePairs bytes n hlength
  have hslice :
      Slices.ByteSlice (α := α) memId v (pairBytes (decodePairs bytes)) =
        Slices.ByteSlice memId v bytes :=
    congrArg (fun chunk => Slices.ByteSlice (α := α) memId v chunk) hdecode.1
  iintro Hslice
  iexists decodePairs bytes
  isplitl_pureexact hdecode.2
  · unfold PairSlice
    irw_exact [hslice] with Hslice

end Ownership

end Wasm.RustStd.HashMap.Table
