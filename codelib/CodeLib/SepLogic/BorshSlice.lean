import CodeLib.SepLogic.ByteSlice
import CodeLib.RustStd.Borsh

/-!
# Borsh layouts as byte slices

`CodeLib.RustStd.Borsh` names the five borsh layouts as byte lists.  This
module states each layout as memory ownership: a `ByteSlice` that holds a
borsh value is the same ownership as the words and bytes the value is made
of.  A driver proof reads the input buffer as a slice, splits it into a
header word and word cells with these lemmas, and joins the output buffer
back with the same lemmas in the other direction.

* `ByteSlice_borsh_u32`: a `u32` is one `pointsTo_u32`.
* `ByteSlice_borsh_bool`, `ByteSlice_borsh_option_none`: one tag byte.
* `ByteSlice_borsh_option_some`: the tag byte `1`, then the payload slice.
* `ByteSlice_borsh_vec`: the `u32` element count, then the packed elements
  as a slice.  `ByteSlice_borsh_vec_words` reads the elements as a
  `WordSlice` when the payload address is four-aligned.
* A tuple is `++`, so a tuple is `ByteSlice_append`.  There is no tuple
  lemma.

The reader direction is pure.  `Borsh.vec?_eq_some` says that a byte list
that `Borsh.vec?` accepts is the encoding of the vector it returns.  With
it, a contract that reads its input through `Borsh.vec?` owns that input as
`Borsh.vec`, and `ByteSlice_borsh_vec` applies.  The lemma comes from
`WordCodec.serialize_of_deserialize_eq_some`, the inverse of
`WordCodec.deserialize_serialize` for a codec whose `encode` undoes `decode`
on every chunk of the right width.

The slice lemmas live in `Wasm.SepLogic.Slices`, next to the slices they
describe.
-/

namespace Wasm.WordCodec

variable {W : Type}

/-- Deserialization is injective on its accepted inputs when `encode` undoes
`decode` on every chunk of width `codec.width`.  This is the inverse of
`deserialize_serialize`. -/
theorem serialize_of_deserialize_eq_some (codec : WordCodec W)
    (hinv : ∀ chunk : List UInt8, chunk.length = codec.width →
      codec.encode (codec.decode chunk) = chunk) :
    ∀ (values : List W) (bytes : List UInt8),
      codec.deserialize bytes = some values → codec.serialize values = bytes := by
  intro values
  induction values with
  | nil =>
      intro bytes h
      cases bytes with
      | nil => rfl
      | cons first rest =>
          rw [deserialize] at h
          split at h
          · simp at h
          · obtain ⟨_, _, htail⟩ := Option.map_eq_some_iff.mp h
            exact absurd htail (List.cons_ne_nil _ _)
  | cons value values ih =>
      intro bytes h
      cases bytes with
      | nil => simp at h
      | cons first rest =>
          rw [deserialize] at h
          split at h
          · simp at h
          · rename_i hlong
            obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp h
            obtain ⟨hvalue, htailEq⟩ := List.cons.inj hcons
            have hchunk : ((first :: rest).take codec.width).length = codec.width := by
              simp only [List.length_take]; omega
            subst htailEq
            rw [serialize_cons, ← hvalue, hinv _ hchunk, ih _ htail]
            exact List.take_append_drop _ _

end Wasm.WordCodec

namespace Wasm.RustStd.Borsh

/-- A `Vec<u32>` occupies four header bytes and four bytes per element. -/
theorem vec_u32le_length (values : List UInt32) :
    (vec WordCodec.u32le values).length = 4 + 4 * values.length :=
  Vec.serialize_length WordCodec.u32le values

/-- A byte list that `vec?` accepts is the encoding of the vector it
returns.  This is the reader direction of `vec?_vec`. -/
theorem vec?_eq_some (bytes : List UInt8) (values : List UInt32)
    (h : vec? WordCodec.u32le bytes = some values) :
    bytes = vec WordCodec.u32le values := by
  unfold vec? Vec.deserialize at h
  split at h
  · simp at h
  · rename_i hlong
    split at h
    · simp at h
    · rename_i decoded hdecoded
      split at h
      · rename_i hcount
        have hvalues : decoded = values := Option.some.inj h
        rw [← hvalues]
        have htake : (bytes.take 4).length = 4 := by
          simp only [List.length_take]; omega
        have hhead :
            WordCodec.u32le.encode (UInt32.ofNat decoded.length) = bytes.take 4 := by
          rw [hcount, UInt32.ofNat_toNat]
          exact SepLogic.Slices.encodeU32_decodeU32_of_length _ htake
        have hpayload : WordCodec.u32le.serialize decoded = bytes.drop 4 :=
          WordCodec.serialize_of_deserialize_eq_some WordCodec.u32le
            (fun chunk hchunk => SepLogic.Slices.encodeU32_decodeU32_of_length chunk hchunk)
            decoded (bytes.drop 4) hdecoded
        unfold vec Vec.serialize
        rw [hhead, hpayload, List.take_append_drop]
      · simp at h

end Wasm.RustStd.Borsh

namespace Wasm.SepLogic.Slices

open Iris Std
open Wasm.RustStd

variable {α : Type} [WasmHeapGS α]

/-- A one-byte slice is one owned byte. -/
theorem ByteSlice_singleton (memId : Nat) (ptr : UInt32) (byte : UInt8) :
    ByteSlice (α := α) memId ptr [byte] ⊣⊢
      iprop(⌜ptr.toNat + 1 < UInt32.size⌝ ∗ (⟨memId, ptr⟩ ↦w byte)) := by
  unfold ByteSlice
  exact BI.sep_congr .rfl
    ((pointsToBytes_cons memId ptr byte []).trans
      ((BI.sep_congr_right (pointsToBytes_nil memId (ptr + 1))).trans BI.sep_emp))

/-- A borsh `u32` is one owned word. -/
theorem ByteSlice_borsh_u32 (memId : Nat) (ptr value : UInt32) :
    ByteSlice (α := α) memId ptr (Borsh.u32 value) ⊣⊢
      iprop(⌜ptr.toNat + 4 < UInt32.size⌝ ∗ pointsTo_u32 memId ptr value) := by
  unfold ByteSlice
  rw [show Borsh.u32 value =
      [u32Byte value 0, u32Byte value 1, u32Byte value 2, u32Byte value 3]
    from encodeU32_eq_u32Bytes value]
  exact BI.sep_congr .rfl (pointsTo_u32_as_bytes memId ptr value).symm

/-- A borsh `bool` is one owned tag byte. -/
theorem ByteSlice_borsh_bool (memId : Nat) (ptr : UInt32) (value : Bool) :
    ByteSlice (α := α) memId ptr (Borsh.bool value) ⊣⊢
      iprop(⌜ptr.toNat + 1 < UInt32.size⌝ ∗
        (⟨memId, ptr⟩ ↦w (if value then 1 else 0))) := by
  unfold Borsh.bool
  exact ByteSlice_singleton memId ptr _

/-- A borsh `None` is one owned tag byte `0`. -/
theorem ByteSlice_borsh_option_none {W : Type} (memId : Nat) (ptr : UInt32)
    (encode : W → List UInt8) :
    ByteSlice (α := α) memId ptr (Borsh.option encode none) ⊣⊢
      iprop(⌜ptr.toNat + 1 < UInt32.size⌝ ∗ (⟨memId, ptr⟩ ↦w 0)) := by
  unfold Borsh.option
  exact ByteSlice_singleton memId ptr 0

/-- A borsh `Some` is the owned tag byte `1`, then the payload slice at the
next address. -/
theorem ByteSlice_borsh_option_some {W : Type} (memId : Nat) (ptr : UInt32)
    (encode : W → List UInt8) (value : W) :
    ByteSlice (α := α) memId ptr (Borsh.option encode (some value)) ⊣⊢
      iprop(⌜ptr.toNat + 1 < UInt32.size⌝ ∗ (⟨memId, ptr⟩ ↦w 1) ∗
        ByteSlice memId (ptr + 1) (encode value)) := by
  have hsplit := ByteSlice_append (α := α) memId ptr [1] (encode value)
  rw [List.singleton_append, List.length_singleton,
    show UInt32.ofNat 1 = (1 : UInt32) from rfl] at hsplit
  exact (hsplit.trans
    (BI.sep_congr_left (ByteSlice_singleton memId ptr 1))).trans BI.sep_assoc

/-- A borsh `Vec<u32>` is the owned element count, then the packed elements
as a slice four bytes later. -/
theorem ByteSlice_borsh_vec (memId : Nat) (ptr : UInt32) (values : List UInt32) :
    ByteSlice (α := α) memId ptr (Borsh.vec WordCodec.u32le values) ⊣⊢
      iprop(⌜ptr.toNat + 4 < UInt32.size⌝ ∗
        pointsTo_u32 memId ptr (UInt32.ofNat values.length) ∗
        ByteSlice memId (ptr + 4) (WordCodec.u32le.serialize values)) := by
  have hsplit := ByteSlice_append (α := α) memId ptr
    (Borsh.u32 (UInt32.ofNat values.length)) (WordCodec.u32le.serialize values)
  rw [show (Borsh.u32 (UInt32.ofNat values.length)).length = 4 from rfl,
    show UInt32.ofNat 4 = (4 : UInt32) from rfl] at hsplit
  exact (hsplit.trans
    (BI.sep_congr_left (ByteSlice_borsh_u32 memId ptr _))).trans BI.sep_assoc

/-- A borsh `Vec<u32>` at a four-aligned address is the owned element count,
then a word slice four bytes later. -/
theorem ByteSlice_borsh_vec_words (memId : Nat) (ptr : UInt32)
    (values : List UInt32) (halign : ptr.toNat % 4 = 0) :
    ByteSlice (α := α) memId ptr (Borsh.vec WordCodec.u32le values) ⊣⊢
      iprop(⌜ptr.toNat + 4 < UInt32.size⌝ ∗
        pointsTo_u32 memId ptr (UInt32.ofNat values.length) ∗
        WordSlice memId (ptr + 4) values) := by
  refine (ByteSlice_borsh_vec memId ptr values).trans ?_
  have halign' : ∀ _hnowrap : ptr.toNat + 4 < UInt32.size,
      (ptr + 4).toNat % 4 = 0 := by
    intro hnowrap
    have h := byteOffset_toNat ptr 4 hnowrap
    rw [show UInt32.ofNat 4 = (4 : UInt32) from rfl] at h
    rw [h]; omega
  constructor
  · iintro ⟨%hnowrap, Hhead, Hpayload⟩
    isplitl_pureexact hnowrap
    isplitl_exact Hhead
    iapply (ByteSlice_serialize_as_WordSlice memId (ptr + 4) values
      (halign' hnowrap)).mp
    iexact Hpayload
  · iintro ⟨%hnowrap, Hhead, Hwords⟩
    isplitl_pureexact hnowrap
    isplitl_exact Hhead
    iapply (ByteSlice_serialize_as_WordSlice memId (ptr + 4) values
      (halign' hnowrap)).mpr
    iexact Hwords

end Wasm.SepLogic.Slices
