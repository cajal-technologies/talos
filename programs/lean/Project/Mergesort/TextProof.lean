import Project.Mergesort.Pure
import Mathlib.Data.Nat.Digits.Defs

/-!
# Text boundary facts for mergesort

The unchanged Rust entry point reads a nonempty sequence of decimal `u64`
tokens separated by the single character `' '`, and prints values in the same
format.  This file records the pure string facts needed to connect that
boundary to the list-level merge-sort theorem.

`String.toNat?` is executable but currently has very little theorem support.
For proofs, `parseUInt64?` below gives the corresponding mathematical parser:
it checks that a token is nonempty and decimal, evaluates the usual base-ten
fold, and rejects values outside the `UInt64` range.
-/

namespace Project.Mergesort.TextProof

/-- Format a list exactly as the Rust entry point does: one ASCII space
between decimal values and no leading or trailing delimiter. -/
def renderValues (values : List UInt64) : String :=
  String.intercalate " " (values.map toString)

/-- Copy the slices produced by Rust-style character splitting into strings. -/
def splitSpaces (text : String) : List String :=
  (text.split ' ').toList.map (·.copy)

/-- Mathematical value of a decimal token, expressed as the same left-to-right
base-ten fold used by standard parsers. -/
def decimalNat (token : String) : Nat :=
  Nat.ofDigitChars 10 token.toList 0

/-- The lexical condition accepted by the proof-level decimal parser. -/
abbrev IsDecimalToken (token : String) : Prop :=
  token ≠ "" ∧ ∀ c ∈ token.toList, c.isDigit

/-- A proof-friendly specification for parsing one `UInt64` token. -/
def parseUInt64? (token : String) : Option UInt64 :=
  if _hdecimal : IsDecimalToken token then
    let value := decimalNat token
    if value < UInt64.size then some (UInt64.ofNat value) else none
  else
    none

@[simp] theorem renderValues_nil : renderValues [] = "" := by
  simp [renderValues]

@[simp] theorem renderValues_singleton (value : UInt64) :
    renderValues [value] = toString value := by
  simp [renderValues]

@[simp] theorem splitSpaces_empty : splitSpaces "" = [""] := by
  simp [splitSpaces]

/-- Splitting on spaces and joining with spaces is a round trip for every
string, including strings with leading, trailing, or repeated spaces. -/
theorem intercalate_splitSpaces (text : String) :
    String.intercalate " " (splitSpaces text) = text := by
  apply String.toList_inj.mp
  simp only [String.toList_intercalate, splitSpaces, List.map_map,
    String.toList_split_char]
  simp

/-- Decimal rendering never emits the separator character. -/
theorem space_not_mem_toString (value : UInt64) :
    ' ' ∉ (toString value).toList := by
  intro hspace
  change ' ' ∈ (toString value.toNat).toList at hspace
  rw [Nat.toString_eq_repr, Nat.toList_repr] at hspace
  have hdigit : ' '.isDigit :=
    Nat.isDigit_of_mem_toDigits (by decide) (by decide) hspace
  simp at hdigit

/-- Every character emitted by decimal `UInt64` formatting is a digit. -/
theorem isDigit_of_mem_toString (value : UInt64) {c : Char}
    (hc : c ∈ (toString value).toList) : c.isDigit := by
  change c ∈ (toString value.toNat).toList at hc
  rw [Nat.toString_eq_repr, Nat.toList_repr] at hc
  exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc

theorem toString_ne_empty (value : UInt64) :
    toString value ≠ "" := by
  change toString value.toNat ≠ ""
  exact Nat.repr_ne_empty

/-- Every `u64` has at most twenty decimal digits.  This is the allocator and
buffer-size bridge used by the bounded exported specification. -/
theorem toString_length_le_twenty (value : UInt64) :
    (toString value).length ≤ 20 := by
  change (Nat.repr value.toNat).length ≤ 20
  apply Nat.repr_length value.toNat 20 (by decide)
  have hvalue : value.toNat < UInt64.size := UInt64.toNat_lt value
  exact hvalue.trans_le (by decide)

theorem isDecimalToken_toString (value : UInt64) :
    IsDecimalToken (toString value) := by
  constructor
  · exact toString_ne_empty value
  · intro c hc
    exact isDigit_of_mem_toString value hc

/-- On nonempty inputs, splitting the formatted stream recovers precisely the
decimal token for each input value. -/
theorem splitSpaces_renderValues (values : List UInt64) (hvalues : values ≠ []) :
    splitSpaces (renderValues values) = values.map toString := by
  unfold splitSpaces renderValues
  change
    ((String.intercalate (String.singleton ' ') (values.map toString)).split ' ').toList.map
        (·.copy) =
      values.map toString
  rw [String.toList_split_intercalate]
  · simp [hvalues]
  · intro token htoken
    simp only [List.mem_map] at htoken
    obtain ⟨value, _, rfl⟩ := htoken
    exact space_not_mem_toString value

@[simp] theorem splitSpaces_renderValues_cons (value : UInt64) (values : List UInt64) :
    splitSpaces (renderValues (value :: values)) =
      (value :: values).map toString := by
  exact splitSpaces_renderValues _ (by simp)

theorem splitSpaces_renderValues_length (values : List UInt64) (hvalues : values ≠ []) :
    (splitSpaces (renderValues values)).length = values.length := by
  rw [splitSpaces_renderValues values hvalues, List.length_map]

/-- The decimal fold evaluates the canonical rendering to its original
mathematical value. -/
@[simp] theorem decimalNat_toString (value : UInt64) :
    decimalNat (toString value) = value.toNat := by
  unfold decimalNat
  change Nat.ofDigitChars 10 (toString value.toNat).toList 0 = value.toNat
  rw [Nat.toString_eq_repr, Nat.toList_repr]
  exact Nat.ofDigitChars_ten_toDigits

/-- The proof-level parser accepts every string emitted by `UInt64` formatting
and returns the original value, including `UInt64.max`. -/
@[simp] theorem parseUInt64?_toString (value : UInt64) :
    parseUInt64? (toString value) = some value := by
  unfold parseUInt64?
  rw [dif_pos]
  · have hlt : decimalNat (toString value) < UInt64.size := by
      rw [decimalNat_toString]
      simpa [UInt64.size] using UInt64.toNat_lt value
    rw [if_pos hlt, decimalNat_toString, UInt64.ofNat_toNat]
  · exact isDecimalToken_toString value

@[simp] theorem parseUInt64?_empty : parseUInt64? "" = none := by
  simp [parseUInt64?, IsDecimalToken]

theorem parseUInt64?_eq_some_iff (token : String) (value : UInt64) :
    parseUInt64? token = some value ↔
      IsDecimalToken token ∧ decimalNat token < UInt64.size ∧
        UInt64.ofNat (decimalNat token) = value := by
  unfold parseUInt64?
  by_cases hdecimal : IsDecimalToken token
  · rw [dif_pos hdecimal]
    by_cases hrange : decimalNat token < UInt64.size
    · rw [if_pos hrange]
      constructor
      · intro heq
        exact ⟨hdecimal, hrange, Option.some.inj heq⟩
      · intro h
        exact congrArg some h.2.2
    · rw [if_neg hrange]
      simp [hrange]
  · rw [dif_neg hdecimal]
    simp [hdecimal]

/-- Parsing all canonical tokens is pointwise successful. -/
@[simp] theorem map_parseUInt64?_toString (values : List UInt64) :
    (values.map toString).map parseUInt64? = values.map some := by
  simp [List.map_map]

@[simp] theorem mapM_parseUInt64?_toString (values : List UInt64) :
    List.mapM parseUInt64? (values.map toString) = some values := by
  induction values with
  | nil => simp
  | cons value values ih => simp [ih]

/-- The complete nonempty input boundary splits and parses back to the input
list.  The nonempty premise is essential: Rust's `"".split(' ')` produces one
empty token, whose `parse::<u64>().unwrap()` panics. -/
theorem parse_split_renderValues (values : List UInt64) (hvalues : values ≠ []) :
    (splitSpaces (renderValues values)).map parseUInt64? = values.map some := by
  rw [splitSpaces_renderValues values hvalues]
  exact map_parseUInt64?_toString values

theorem collect_parse_split_renderValues (values : List UInt64) (hvalues : values ≠ []) :
    List.mapM parseUInt64? (splitSpaces (renderValues values)) = some values := by
  rw [splitSpaces_renderValues values hvalues]
  exact mapM_parseUInt64?_toString values

/-- `Pure.encodeValues` is exactly the UTF-8 byte representation of the text
format used in this file. -/
theorem encodeValues_eq_toUTF8 (values : List UInt64) :
    Pure.encodeValues values = (renderValues values).toUTF8.toList := by
  rfl

end Project.Mergesort.TextProof
