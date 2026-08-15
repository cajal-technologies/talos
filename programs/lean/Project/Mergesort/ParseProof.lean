import Project.Mergesort.TextProof
import Project.Mergesort.ParseByteProof
import Project.Mergesort.WideMulProof
import Project.Mergesort.MemoryFillProof
import CodeLib.Examples.SelectionSort.TotalProof

/-!
# Generated decimal `u64` parser proof

The successful driver path crosses three thin generated wrappers before it
reaches the large radix parser:

* local `func81` (`str::parse`) calls absolute index `55` (`func53`);
* local `func53` (`u64::from_str`) supplies radix ten and calls absolute
  index `53` (`func51`);
* local `func2` is the iterator-map closure which calls absolute index `83`
  (`func81`) and unwraps the successful result.

The forwarding rules below expose those exact call sites.  Thus the eventual
`func51` theorem can be composed without re-unfolding any wrapper.  Its
successful call contract will write discriminant byte zero at the caller's
result address and the parsed `u64` eight bytes later.
-/

namespace Project.Mergesort.ParseProof

open Wasm
open Iris Iris.ProgramLogic Language.Notation Std
open Wasm.SepLogic Wasm.SmallStep
open Project.Mergesort.FunctionSpecs
open Project.Mergesort.Machine
open Project.Mergesort.RangeProof
open Project.Mergesort.ParseByteProof
open Project.Mergesort.TextProof
open Project.Mergesort.WideMulProof
open Project.Mergesort.MemoryFillProof

/-! ## Mathematical invariant for the generated digit loops -/

/-- Numeric value assigned to an ASCII decimal character by the generated
`func52` helper on its successful radix-ten path. -/
def digitNat (c : Char) : Nat := c.toNat - '0'.toNat

/-- The accumulator update performed by both successful digit loops in
`func51`.  The Wasm uses `acc * radix + digit`; the wrapper fixes `radix = 10`.
-/
def nextAccumulator (acc : Nat) (c : Char) : Nat :=
  acc * 10 + digitNat c

/-- Pure state of either generated decimal loop.  `consumed` and `remaining`
correspond to the prefix already traversed and the pointer/length pair stored
at frame offsets 48 and 52.  `acc` corresponds to the `u64` at offset 112.
-/
def DecimalLoopInvariant
    (token : String) (consumed remaining : List Char) (acc : Nat) : Prop :=
  IsDecimalToken token ∧
  token.toList = consumed ++ remaining ∧
  acc = Nat.ofDigitChars 10 consumed 0 ∧
  acc < UInt64.size

theorem decimalLoopInvariant_start {token : String}
    (hdecimal : IsDecimalToken token) :
    DecimalLoopInvariant token [] token.toList 0 := by
  exact ⟨hdecimal, by simp, by simp [Nat.ofDigitChars], by decide⟩

theorem DecimalLoopInvariant.remaining_length
    {token : String} {consumed remaining : List Char} {acc : Nat}
    (h : DecimalLoopInvariant token consumed remaining acc) :
    consumed.length + remaining.length = token.toList.length := by
  rw [h.2.1]
  simp

theorem DecimalLoopInvariant.head_isDigit
    {token : String} {consumed rest : List Char} {acc : Nat} {c : Char}
    (h : DecimalLoopInvariant token consumed (c :: rest) acc) :
    c.isDigit := by
  exact h.1.2 c (by rw [h.2.1]; simp)

theorem DecimalLoopInvariant.measure_decreases
    {token : String} {consumed rest : List Char} {acc : Nat} {c : Char}
    (_h : DecimalLoopInvariant token consumed (c :: rest) acc) :
    rest.length < (c :: rest).length := by
  simp

private theorem ofDigitChars_append (left right : List Char) (init : Nat) :
    Nat.ofDigitChars 10 (left ++ right) init =
      Nat.ofDigitChars 10 right (Nat.ofDigitChars 10 left init) := by
  simp [Nat.ofDigitChars, List.foldl_append]

private theorem ofDigitChars_ten_init_le (chars : List Char) (init : Nat) :
    init ≤ Nat.ofDigitChars 10 chars init := by
  induction chars generalizing init with
  | nil => simp [Nat.ofDigitChars]
  | cons c chars ih =>
      rw [show Nat.ofDigitChars 10 (c :: chars) init =
          Nat.ofDigitChars 10 chars (10 * init + digitNat c) by
        simp [Nat.ofDigitChars, digitNat]]
      exact (by omega : init ≤ 10 * init + digitNat c).trans (ih _)

/-- One successful generated loop iteration preserves the invariant whenever
the checked arithmetic path establishes that the next value fits in `u64`. -/
theorem DecimalLoopInvariant.takeDigit
    {token : String} {consumed rest : List Char} {acc : Nat} {c : Char}
    (h : DecimalLoopInvariant token consumed (c :: rest) acc)
    (hnext : nextAccumulator acc c < UInt64.size) :
    DecimalLoopInvariant token (consumed ++ [c]) rest
      (nextAccumulator acc c) := by
  rcases h with ⟨hdecimal, hparts, hacc, _hbound⟩
  refine ⟨hdecimal, ?_, ?_, hnext⟩
  · simpa [List.append_assoc] using hparts
  · rw [hacc, ofDigitChars_append]
    simp [Nat.ofDigitChars, nextAccumulator, digitNat, Nat.mul_comm]

/-- Every accumulator belonging to a prefix of a canonical `UInt64` decimal
rendering still fits in `UInt64`.  This discharges all checked-multiply and
checked-add branches on the program's actual input language. -/
theorem canonicalPrefix_lt_size (value : UInt64)
    (consumed remaining : List Char)
    (hparts : (toString value).toList = consumed ++ remaining) :
    Nat.ofDigitChars 10 consumed 0 < UInt64.size := by
  have hle := ofDigitChars_ten_init_le remaining
    (Nat.ofDigitChars 10 consumed 0)
  rw [← ofDigitChars_append] at hle
  have hfull : Nat.ofDigitChars 10 (consumed ++ remaining) 0 = value.toNat := by
    rw [← hparts]
    exact decimalNat_toString value
  rw [hfull] at hle
  exact hle.trans_lt (UInt64.toNat_lt value)

/-- Canonical tokens preserve the loop invariant without an extra arithmetic
premise: prefix boundedness follows from the final rendered `UInt64` value. -/
theorem DecimalLoopInvariant.takeCanonicalDigit
    {value : UInt64} {consumed rest : List Char} {acc : Nat} {c : Char}
    (h : DecimalLoopInvariant (toString value) consumed (c :: rest) acc) :
    DecimalLoopInvariant (toString value) (consumed ++ [c]) rest
      (nextAccumulator acc c) := by
  apply h.takeDigit
  have hnextEq : nextAccumulator acc c =
      Nat.ofDigitChars 10 (consumed ++ [c]) 0 := by
    rw [h.2.2.1, ofDigitChars_append]
    simp [Nat.ofDigitChars, nextAccumulator, digitNat, Nat.mul_comm]
  rw [hnextEq]
  apply canonicalPrefix_lt_size value (consumed ++ [c]) rest
  calc
    (toString value).toList = consumed ++ c :: rest := h.2.1
    _ = (consumed ++ [c]) ++ rest := by simp [List.append_assoc]

theorem DecimalLoopInvariant.finished_decimalNat
    {token : String} {consumed : List Char} {acc : Nat}
    (h : DecimalLoopInvariant token consumed [] acc) :
    decimalNat token = acc := by
  unfold decimalNat
  rw [h.2.1]
  simp [h.2.2.1]

/-- At loop exhaustion, the invariant yields exactly `TextProof.parseUInt64?`'s
successful result. -/
theorem DecimalLoopInvariant.finished_parse
    {token : String} {consumed : List Char} {acc : Nat}
    (h : DecimalLoopInvariant token consumed [] acc) :
    parseUInt64? token = some (UInt64.ofNat acc) := by
  rw [parseUInt64?_eq_some_iff]
  exact ⟨h.1, by simpa [h.finished_decimalNat] using h.2.2.2,
    by simp [h.finished_decimalNat]⟩

/-! ## UInt64 representation used by generated `func51` -/

/-- The actual `i64.mul`/`i64.add` update emitted in the parser loops. -/
def machineNextAccumulator (acc : UInt64) (c : Char) : UInt64 :=
  acc * UInt64.ofNat 10 + UInt64.ofNat (digitNat c)

/-- Under the checked-path bound, the Wasm-width update represents the
mathematical decimal update exactly, with no modular wraparound. -/
theorem machineNextAccumulator_toNat
    (acc : UInt64) (c : Char)
    (hnext : nextAccumulator acc.toNat c < UInt64.size) :
    (machineNextAccumulator acc c).toNat = nextAccumulator acc.toNat c := by
  have hten : (10 : Nat) < UInt64.size := by decide
  have hdigit : digitNat c < UInt64.size := by
    have hle : digitNat c ≤ nextAccumulator acc.toNat c := by
      simp [nextAccumulator]
    exact hle.trans_lt hnext
  have hmul : acc.toNat * 10 < UInt64.size := by
    unfold nextAccumulator at hnext
    omega
  simp only [machineNextAccumulator, UInt64.toNat_add, UInt64.toNat_mul]
  rw [UInt64.toNat_ofNat_of_lt' hten,
    UInt64.toNat_ofNat_of_lt' hdigit,
    Nat.mod_eq_of_lt hmul]
  rw [Nat.mod_eq_of_lt]
  · rfl
  · simpa [nextAccumulator] using hnext

/-- Loop invariant stated with the concrete `UInt64` accumulator stored at
generated frame offset 112. -/
def DecimalMachineLoopInvariant
    (token : String) (consumed remaining : List Char) (acc : UInt64) : Prop :=
  DecimalLoopInvariant token consumed remaining acc.toNat

theorem decimalMachineLoopInvariant_start {token : String}
    (hdecimal : IsDecimalToken token) :
    DecimalMachineLoopInvariant token [] token.toList 0 := by
  simpa [DecimalMachineLoopInvariant] using decimalLoopInvariant_start hdecimal

theorem DecimalMachineLoopInvariant.takeDigit
    {token : String} {consumed rest : List Char} {acc : UInt64} {c : Char}
    (h : DecimalMachineLoopInvariant token consumed (c :: rest) acc)
    (hnext : nextAccumulator acc.toNat c < UInt64.size) :
    DecimalMachineLoopInvariant token (consumed ++ [c]) rest
      (machineNextAccumulator acc c) := by
  unfold DecimalMachineLoopInvariant at h ⊢
  rw [machineNextAccumulator_toNat acc c hnext]
  exact h.takeDigit hnext

theorem DecimalMachineLoopInvariant.takeCanonicalDigit
    {value : UInt64} {consumed rest : List Char} {acc : UInt64} {c : Char}
    (h : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc) :
    DecimalMachineLoopInvariant (toString value) (consumed ++ [c]) rest
      (machineNextAccumulator acc c) := by
  have hpure :=
    (show DecimalLoopInvariant
      (toString value) consumed (c :: rest) acc.toNat from h).takeCanonicalDigit
  have hnext : nextAccumulator acc.toNat c < UInt64.size := hpure.2.2.2
  unfold DecimalMachineLoopInvariant
  rw [machineNextAccumulator_toNat acc c hnext]
  exact hpure

theorem DecimalMachineLoopInvariant.finished_parse
    {token : String} {consumed : List Char} {acc : UInt64}
    (h : DecimalMachineLoopInvariant token consumed [] acc) :
    parseUInt64? token = some acc := by
  have hparse :=
    (show DecimalLoopInvariant token consumed [] acc.toNat from h).finished_parse
  simpa [UInt64.ofNat_toNat] using hparse

/-! ## Canonical token dispatch and total digit traversal -/

/-- A canonical `UInt64` rendering takes the generated parser's nonempty,
unsigned branch.  In particular its first byte is neither accepted sign
character. -/
theorem canonicalToken_unsigned_dispatch (value : UInt64) :
    ∃ c rest, (toString value).toList = c :: rest ∧ c ≠ '+' ∧ c ≠ '-' := by
  have hne : (toString value).toList ≠ [] := by
    intro h
    apply toString_ne_empty value
    apply String.ext
    simpa using h
  obtain ⟨c, rest, hlist⟩ := List.exists_cons_of_ne_nil hne
  refine ⟨c, rest, hlist, ?_, ?_⟩
  · have hdigit := isDigit_of_mem_toString value
      (show c ∈ (toString value).toList by rw [hlist]; simp)
    intro h
    subst c
    simp [Char.isDigit] at hdigit
  · have hdigit := isDigit_of_mem_toString value
      (show c ∈ (toString value).toList by rw [hlist]; simp)
    intro h
    subst c
    simp [Char.isDigit] at hdigit

/-- One exact canonical digit iteration, stated at the generated machine
width.  It both identifies the next `i64.mul`/`i64.add` accumulator and proves
the strict decrease used by the total loop. -/
theorem canonicalDigitIteration_exact
    {value : UInt64} {consumed rest : List Char} {acc : UInt64} {c : Char}
    (h : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc) :
    let next := machineNextAccumulator acc c
    DecimalMachineLoopInvariant
      (toString value) (consumed ++ [c]) rest next ∧
    (toString value).length - (consumed ++ [c]).length <
      (toString value).length - consumed.length := by
  dsimp only
  constructor
  · exact h.takeCanonicalDigit
  · have hlength :=
      (show DecimalLoopInvariant
        (toString value) consumed (c :: rest) acc.toNat from h).remaining_length
    rw [String.length_toList] at hlength
    rw [← hlength]
    simp
    omega

/-- The concrete `i32` value produced by the generated `load8_u` for an
ASCII character in the canonical token. -/
def asciiByte32 (c : Char) : UInt32 :=
  (UInt8.ofNat c.toNat).toUInt32

/-- All arithmetic side conditions needed by the `func52` call in one
canonical digit iteration. -/
theorem canonicalDigitByteFacts
    {value acc : UInt64} {consumed rest : List Char} {c : Char}
    (h : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc) :
    asciiByte32 c ≤ 57 ∧ asciiByte32 c - 48 < 10 ∧
      UInt64.ofNat (asciiByte32 c - 48).toNat =
        UInt64.ofNat (digitNat c) := by
  have hdigit : c.isDigit :=
    (show DecimalLoopInvariant
      (toString value) consumed (c :: rest) acc.toNat from h).head_isDigit
  have hc := Char.isDigit_iff_toNat.mp hdigit
  have hzero : '0'.toNat = 48 := by decide
  have hnine : '9'.toNat = 57 := by decide
  have hcsmall : c.toNat < 256 := by omega
  have hbyte : (UInt8.ofNat c.toNat).toNat = c.toNat := by
    rw [show (UInt8.ofNat c.toNat).toNat = c.toNat % 256 by rfl,
      Nat.mod_eq_of_lt hcsmall]
  have hsubNat : (asciiByte32 c - 48).toNat = digitNat c := by
    simp only [asciiByte32, UInt32.toNat_sub,
      UInt8.toUInt32_toNat, hbyte]
    rw [show (48 : UInt32).toNat = 48 by decide]
    simp only [digitNat, hzero]
    have heq : 2 ^ 32 - 48 + c.toNat =
        (c.toNat - 48) + 2 ^ 32 := by omega
    rw [heq, Nat.add_mod_right]
    rw [Nat.mod_eq_of_lt (show c.toNat - 48 < 2 ^ 32 by omega)]
  refine ⟨?_, ?_, by rw [hsubNat]⟩
  · rw [UInt32.le_iff_toNat_le]
    simp only [asciiByte32, UInt8.toUInt32_toNat, hbyte]
    rw [show (57 : UInt32).toNat = 57 by decide]
    omega
  · rw [UInt32.lt_iff_toNat_lt, hsubNat]
    rw [show (10 : UInt32).toNat = 10 by decide]
    simp only [digitNat, hzero]
    omega

theorem canonicalDigitByte_mask
    {value acc : UInt64} {consumed rest : List Char} {c : Char}
    (h : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc) :
    asciiByte32 c &&& 255 = asciiByte32 c := by
  have hdigit : c.isDigit :=
    (show DecimalLoopInvariant
      (toString value) consumed (c :: rest) acc.toNat from h).head_isDigit
  have hc := Char.isDigit_iff_toNat.mp hdigit
  have hzero : '0'.toNat = 48 := by decide
  have hnine : '9'.toNat = 57 := by decide
  have hcases : c.toNat = 48 ∨ c.toNat = 49 ∨ c.toNat = 50 ∨
      c.toNat = 51 ∨ c.toNat = 52 ∨ c.toNat = 53 ∨
      c.toNat = 54 ∨ c.toNat = 55 ∨ c.toNat = 56 ∨
      c.toNat = 57 := by
    omega
  rcases hcases with h | h | h | h | h | h | h | h | h | h <;>
    simp [asciiByte32, h] <;> decide

/-- On a canonical token, the running accumulator always stays small enough
that the generated wide multiply by ten cannot produce a nonzero high word.
The bound is exactly the `wideMul_call_twp` side condition. -/
theorem DecimalMachineLoopInvariant.mulAcc_bound
    {value acc : UInt64} {consumed rest : List Char} {c : Char}
    (h : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc) :
    acc ≤ 1844674407370955161 := by
  have hpure : DecimalLoopInvariant
      (toString value) consumed (c :: rest) acc.toNat := h
  have hnext : nextAccumulator acc.toNat c < UInt64.size :=
    hpure.takeCanonicalDigit.2.2.2
  rw [UInt64.le_iff_toNat_le,
    show (1844674407370955161 : UInt64).toNat = 1844674407370955161 by rfl]
  unfold nextAccumulator at hnext
  simp only [UInt64.size] at hnext ⊢
  omega

/-- On a canonical token, the generated checked add of the decoded digit onto
the multiplied accumulator can never wrap, so its `i64.lt_u` overflow probe
is always false. -/
theorem canonicalDigit_no_add_overflow
    {value acc : UInt64} {consumed rest : List Char} {c : Char}
    (h : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc) :
    ¬ machineNextAccumulator acc c < acc * 10 := by
  have hpure : DecimalLoopInvariant
      (toString value) consumed (c :: rest) acc.toNat := h
  have hnext : nextAccumulator acc.toNat c < UInt64.size :=
    hpure.takeCanonicalDigit.2.2.2
  have hmulNat : acc.toNat * 10 < UInt64.size := by
    unfold nextAccumulator at hnext
    omega
  have hmnat := machineNextAccumulator_toNat acc c hnext
  have hmul : (acc * 10).toNat = acc.toNat * 10 := by
    rw [UInt64.toNat_mul, show ((10 : UInt64)).toNat = 10 from rfl,
      Nat.mod_eq_of_lt hmulNat]
  intro hlt
  rw [UInt64.lt_iff_toNat_lt, hmnat, hmul] at hlt
  unfold nextAccumulator at hlt
  omega

/-- Consume all remaining canonical decimal digits.  The termination measure
is the generated loop's semantic counterpart: token length minus the number
of already consumed characters.  The result packages the final machine
accumulator together with the exhausted-loop invariant. -/
def finishCanonicalDigits (value : UInt64)
    (consumed remaining : List Char) (acc : UInt64)
    (h : DecimalMachineLoopInvariant
      (toString value) consumed remaining acc) :
    { final : UInt64 // DecimalMachineLoopInvariant
        (toString value) (consumed ++ remaining) [] final } :=
  match remaining with
  | [] => ⟨acc, by simpa using h⟩
  | c :: rest => by
      simpa [List.append_assoc] using
        finishCanonicalDigits value (consumed ++ [c]) rest
          (machineNextAccumulator acc c) h.takeCanonicalDigit
termination_by (toString value).length - consumed.length
decreasing_by
  have hlength :=
    (show DecimalLoopInvariant
      (toString value) consumed (c :: rest) acc.toNat from h).remaining_length
  rw [String.length_toList] at hlength
  rw [← hlength]
  simp
  omega

/-- The well-founded digit traversal computes the original `UInt64` exactly.
This is the total loop theorem used to identify the generated success value. -/
theorem finishCanonicalDigits_eq (value : UInt64) :
    (finishCanonicalDigits value [] (toString value).toList 0
      (decimalMachineLoopInvariant_start
        (isDecimalToken_toString value))).1 = value := by
  let final := finishCanonicalDigits value [] (toString value).toList 0
    (decimalMachineLoopInvariant_start (isDecimalToken_toString value))
  have hfinal : DecimalMachineLoopInvariant
      (toString value) (toString value).toList [] final :=
    final.property
  have hparse := hfinal.finished_parse
  rw [parseUInt64?_toString] at hparse
  exact Option.some.inj hparse.symm

/-! ## Generated `func51` frame entry -/

private def fromAsciiRadixParams
    (resultPtr textPtr textLength radix : UInt32) : List Value :=
  [.i32 resultPtr, .i32 textPtr, .i32 textLength, .i32 radix]

private def fromAsciiRadixZeroLocals : List Value :=
  func51Def.locals.map ValueType.zero

private def fromAsciiRadixFramedLocals (frame : UInt32) : List Value :=
  fromAsciiRadixZeroLocals.set 0 (.i32 frame)

/-- Generated body after installing its 144-byte frame and recording the
input pointer/length at frame offsets 48 and 52. -/
def fromAsciiRadixAfterInit : Program := func51.drop 12

/-- Generated body after the successful `2 ≤ radix ≤ 36` validation block. -/
def fromAsciiRadixAfterRadixCheck : Program := func51.drop 13

private theorem parserSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 56 ≤ UInt32.size)
    (hoffset : offset ≤ 52) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hoffset ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  refine ⟨h0, ?_, ?_, ?_⟩
  · simpa using hstep 1 (by omega)
  · simpa using hstep 2 (by omega)
  · simpa using hstep 3 (by omega)

private theorem parserWideSlotFacts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 120 ≤ UInt32.size)
    (hoffset : offset + 4 ≤ 120) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega)⟩

private theorem parserWideSlot64Facts (base : UInt32) (offset : Nat)
    (hroom : base.toNat + 120 ≤ UInt32.size)
    (hoffset : offset + 8 ≤ 120) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 ∧
    ((base + UInt32.ofNat offset) + 4).toNat =
      (base + UInt32.ofNat offset).toNat + 4 ∧
    ((base + UInt32.ofNat offset) + 5).toNat =
      (base + UInt32.ofNat offset).toNat + 5 ∧
    ((base + UInt32.ofNat offset) + 6).toNat =
      (base + UInt32.ofNat offset).toNat + 6 ∧
    ((base + UInt32.ofNat offset) + 7).toNat =
      (base + UInt32.ofNat offset).toNat + 7 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 7) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega),
    by simpa using hstep 4 (by omega), by simpa using hstep 5 (by omega),
    by simpa using hstep 6 (by omega), by simpa using hstep 7 (by omega)⟩

private def decimalDigitLocals
    (frame currentPtr currentLength nextPtr nextLength byte
      temporaryDigit finalDigit : UInt32) : List Value :=
  ((((((((fromAsciiRadixFramedLocals frame).set 26 (.i32 currentPtr)).set 27
    (.i32 currentPtr)).set 28 (.i32 currentLength)).set 29
    (.i32 nextPtr)).set 30 (.i32 nextLength)).set 31 (.i32 byte)).set 32
    (.i32 temporaryDigit)).set 33 (.i32 finalDigit)

/-- Successful result block entered after `func52` has decoded a decimal
byte. -/
def decimalDigitResultBody : Program := [
  .localGet 4, .load32 56, .const 1, .and, .eqz, .br_if 0,
  .localGet 4, .load32 60, .localSet 37,
  .localGet 4, .localGet 4, .load64 112,
  .localGet 37, .extendUI32, .addI64, .store64 112,
  .localGet 4, .localGet 33, .store32 48,
  .localGet 4, .localGet 34, .store32 52,
  .br 1]

/-- Exact generated segment from the prepared byte local through the
successful decoder result and accumulator update. -/
def decimalDigitCallSegment : Program := [
  .localGet 4, .const 8, .add,
  .localGet 35, .localGet 3, .call 54,
  .localGet 4, .load32 12, .localSet 36,
  .localGet 4, .localGet 4, .load32 8, .store32 56,
  .localGet 4, .localGet 36, .store32 60,
  .block 0 0 decimalDigitResultBody]

/-- Generated multiply-and-load prefix immediately before the decoder call
segment. -/
def decimalDigitPrepareSegment : Program := [
  .localGet 4, .localGet 4, .load64 112,
  .localGet 3, .extendUI32, .mulI64, .store64 112,
  .localGet 30, .load8U 0, .const 255, .and, .localSet 35]

/-- Nonempty portion of the generated simple decimal loop, beginning just
after its length guard. -/
def decimalSimpleLoopAfterGuard : Program := [
  .localGet 4, .load32 48, .localSet 30,
  .localGet 4, .load32 48, .localSet 31,
  .localGet 4, .load32 52, .localSet 32,
  .localGet 31, .const 1, .add, .localSet 33,
  .localGet 32, .const 1, .sub, .localSet 34] ++
  decimalDigitPrepareSegment ++ decimalDigitCallSegment

def decimalSimpleLoopBody : Program := [
  .localGet 4, .load32 52, .const 1, .geU,
  .const 1, .and, .eqz, .br_if 3] ++ decimalSimpleLoopAfterGuard

private theorem twp_extendUI32
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {value : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues,
          .i64 (UInt64.ofNat value.toNat) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 value :: values⟩,
        .extendUI32 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.extendUI32)

private theorem twp_addI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs + rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .addI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.addI64)

private theorem twp_mulI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 (lhs * rhs) :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .mulI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.mulI64)

private theorem twp_geU
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≥ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i32 rhs :: .i32 lhs :: values⟩,
        .geU :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.geU hresult)

/-- Total counterpart of the generic partial `i32.load8_u` rule. -/
private theorem twp_load8U
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {address offset : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} (byte : UInt8)
    (hnowrap : (address + offset).toNat =
      address.toNat + offset.toNat) :
    let current : ThreadState α :=
      ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩
    let next : ThreadState α :=
      ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩
    pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
    (pointsTo (GF := WasmHeapGF) (H := WasmHeapMap)
        (address + offset) (DFrac.own 1) (some byte) -∗
      WP (Expr.running next : Expr α) @ s; E [{ Φ }]) -∗
      WP (Expr.running current : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  iintro Hpt Htwp
  iapply twp_lift_step_no_fork rfl
  iintro %store %ns %obs %nt Hσ
  ihave %Hfacts : ⌜store.wasm.mem.read8 (address + offset) = byte ∧
      (address + offset).toNat < store.wasm.mem.pages * 65536⌝ $$
      [Hσ Hpt]
  · imod stateInterp_pointsTo_facts store ns obs nt
      (address + offset) byte $$ [$Hσ $Hpt] with %Hfacts
    ipureintro
    exact Hfacts
  have hbound : address.toNat + offset.toNat + 1 ≤
      store.wasm.mem.pages * 65536 := by
    rw [← hnowrap]
    omega
  iapply fupd_mask_intro Std.LawfulSet.empty_subset
  iintro Hclose
  isplitr
  · ipureintro
    cases s <;> simp only [Stuckness.MaybeReducibleNoObs]
    exact ⟨.running
        ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
          code, arity, remainder, controls, calls⟩,
      store, [], ⟨rfl, .instruction (.load8U offset), rfl,
        by simpa [Hfacts.1] using
          (Step.load8U (α := α) (address := address) hbound)⟩⟩
  iintro %κ %e₂ %store₂ %forks %Hstep
  rcases Hstep with ⟨hforks, _kind, _hobs, wasmStep⟩
  change forks = [] at hforks
  subst forks
  subst κ
  have expectedStep : Step
      ⟨.running ⟨⟨params, localValues, .i32 address :: values⟩,
        .load8U offset :: code, arity, remainder, controls, calls⟩, store⟩
      (.instruction (.load8U offset))
      ⟨.running ⟨⟨params, localValues, .i32 byte.toUInt32 :: values⟩,
        code, arity, remainder, controls, calls⟩, store⟩ := by
    simpa [Hfacts.1] using
      (Step.load8U (α := α) (address := address) hbound)
  obtain ⟨rfl, hconfig⟩ := step_deterministic expectedStep wasmStep
  have parts := Config.mk.inj hconfig
  have hexpr := parts.1
  have hstore := parts.2
  simp only at hexpr hstore
  subst e₂
  subst store₂
  imod Hclose
  imodintro
  isplit
  · ipureintro; rfl
  isplit
  · ipureintro; rfl
  isplitl [Hσ]
  · iexact Hσ
  · iapply Htwp
    iexact Hpt

set_option maxHeartbeats 600000 in
/-- Exact preparation prefix for one canonical decimal digit.  It multiplies
the accumulator by ten and loads/masks the current ASCII byte, preserving the
owned source byte for the loop invariant. -/
theorem decimalDigitPrepareSegment_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame : UInt32)
    (currentPtr currentLength nextPtr nextLength : UInt32)
    (value acc : UInt64) (consumed rest : List Char) (c : Char)
    (oldByte oldTemporary oldFinal : UInt32)
    (hinvariant : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc)
    (hframeRoom : frame.toNat + 120 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u64 (frame + 112) acc ∗
      (currentPtr ↦w (UInt8.ofNat c.toNat)) ∗
      (pointsTo_u64 (frame + 112) (acc * UInt64.ofNat 10) -∗
        (currentPtr + 0 ↦w (UInt8.ofNat c.toNat)) -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              decimalDigitLocals frame currentPtr currentLength
                nextPtr nextLength (asciiByte32 c)
                oldTemporary oldFinal, []⟩,
            decimalDigitCallSegment ++ code,
            arity, remainder, controls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          decimalDigitLocals frame currentPtr currentLength
            nextPtr nextLength oldByte oldTemporary oldFinal, []⟩,
        decimalDigitPrepareSegment ++ decimalDigitCallSegment ++ code,
        arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  obtain ⟨h1120, h1121, h1122, h1123, h1124, h1125, h1126, h1127⟩ :=
    parserWideSlot64Facts frame 112 hframeRoom (by decide)
  have hmask := canonicalDigitByte_mask hinvariant
  iintro ⟨Hacc, Hbyte, Hcont⟩
  simp only [decimalDigitPrepareSegment, List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 acc h1120 h1121 h1122 h1123 h1124
      h1125 h1126 h1127 $$ Hacc
  iintro Hacc
  iapply twp_localGet rfl
  iapply twp_extendUI32
  iapply twp_mulI64
  iapply Wasm.SmallStep.twp_store64 acc h1120 h1121 h1122 h1123 h1124
      h1125 h1126 h1127 $$ Hacc
  iintro Hacc
  iapply twp_localGet rfl
  ihave Hbyte' :
      (currentPtr + 0 ↦w (UInt8.ofNat c.toNat)) $$ [Hbyte]
  · rw [UInt32.add_zero]
    iexact Hbyte
  iapply twp_load8U (UInt8.ofNat c.toNat) (by simp) $$ Hbyte'
  iintro Hbyte
  iapply twp_const
  iapply twp_and
  rw [show (UInt8.ofNat c.toNat).toUInt32 = asciiByte32 c by rfl]
  rw [hmask]
  iapply twp_localSet rfl
  simp only [fromAsciiRadixParams, decimalDigitLocals,
    fromAsciiRadixFramedLocals, fromAsciiRadixZeroLocals, func51Def,
    List.map_cons, List.map_nil, ValueType.zero, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  ihave Hacc' :
      pointsTo_u64 (frame + 112) (acc * UInt64.ofNat 10) $$ [Hacc]
  · rw [show UInt32.ofNat 112 = 112 by decide,
      show (10 : UInt32).toNat = 10 by decide]
    iexact Hacc
  iapply Hcont $$ Hacc' Hbyte

set_option maxHeartbeats 1000000 in
/-- One exact successful canonical-digit segment of generated `func51`.

The byte and the already-multiplied accumulator are the values prepared by
the immediately preceding generated instructions.  This rule crosses the
absolute-index-54 `func52` call, copies its descriptor, takes the successful
block path, adds the decoded digit, and commits the next pointer and length.
It stops at the loop back-edge so a later loop rule can consume the updated
mathematical and machine invariants together. -/
theorem decimalDigitCallSegment_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame : UInt32)
    (currentPtr currentLength nextPtr nextLength byte : UInt32)
    (value acc : UInt64) (consumed rest : List Char) (c : Char)
    (oldTemporary oldFinal : UInt32)
    (oldInner4 oldInner8 oldInner12 : UInt32)
    (oldResult8 oldResult12 oldCopy56 oldCopy60 : UInt32)
    (oldPointer oldLength : UInt32)
    (hbyteNumeric : byte ≤ 57)
    (hdigit : byte - 48 < 10)
    (hdecode : UInt64.ofNat (byte - 48).toNat =
      UInt64.ofNat (digitNat c))
    (hinvariant : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc)
    (hinnerRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hframeRoom : frame.toNat + 120 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      pointsTo_u32 ((frame - 16) + 4) oldInner4 ∗
      pointsTo_u32 ((frame - 16) + 8) oldInner8 ∗
      pointsTo_u32 ((frame - 16) + 12) oldInner12 ∗
      pointsTo_u32 (frame + 8) oldResult8 ∗
      pointsTo_u32 (frame + 12) oldResult12 ∗
      pointsTo_u32 (frame + 56) oldCopy56 ∗
      pointsTo_u32 (frame + 60) oldCopy60 ∗
      pointsTo_u64 (frame + 112) (acc * UInt64.ofNat 10) ∗
      pointsTo_u32 (frame + 48) oldPointer ∗
      pointsTo_u32 (frame + 52) oldLength ∗
      ((⌜DecimalMachineLoopInvariant (toString value)
          (consumed ++ [c]) rest (machineNextAccumulator acc c)⌝ ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 frame) ∗
        pointsTo_u32 ((frame - 16) + 4) 1 ∗
        pointsTo_u32 ((frame - 16) + 8) (byte - 48) ∗
        pointsTo_u32 ((frame - 16) + 12) (byte - 48) ∗
        pointsTo_u32 (frame + 8) 1 ∗
        pointsTo_u32 (frame + 12) (byte - 48) ∗
        pointsTo_u32 (frame + 56) 1 ∗
        pointsTo_u32 (frame + 60) (byte - 48) ∗
        pointsTo_u64 (frame + 112) (machineNextAccumulator acc c) ∗
        pointsTo_u32 (frame + 48) nextPtr ∗
        pointsTo_u32 (frame + 52) nextLength) -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              decimalDigitLocals frame currentPtr currentLength
                nextPtr nextLength byte
                (byte - 48) (byte - 48), []⟩,
            [.br 1], arity, remainder,
            { kind := .block
              paramArity := 0
              resultArity := 0
              body := decimalDigitResultBody
              continuation := code
              belowStack := [] } :: controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          decimalDigitLocals frame currentPtr currentLength
            nextPtr nextLength byte oldTemporary oldFinal, []⟩,
        decimalDigitCallSegment ++ code, arity, remainder, controls, calls⟩ :
        Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h80, h81, h82, h83⟩ :=
    parserWideSlotFacts frame 8 hframeRoom (by decide)
  obtain ⟨h120, h121, h122, h123⟩ :=
    parserWideSlotFacts frame 12 hframeRoom (by decide)
  obtain ⟨h480, h481, h482, h483⟩ :=
    parserWideSlotFacts frame 48 hframeRoom (by decide)
  obtain ⟨h520, h521, h522, h523⟩ :=
    parserWideSlotFacts frame 52 hframeRoom (by decide)
  obtain ⟨h560, h561, h562, h563⟩ :=
    parserWideSlotFacts frame 56 hframeRoom (by decide)
  obtain ⟨h600, h601, h602, h603⟩ :=
    parserWideSlotFacts frame 60 hframeRoom (by decide)
  obtain ⟨h1120, h1121, h1122, h1123, h1124, h1125, h1126, h1127⟩ :=
    parserWideSlot64Facts frame 112 hframeRoom (by decide)
  have hresultRoom : (frame + 8).toNat + 8 ≤ UInt32.size := by
    have h80' : (frame + 8).toNat = frame.toNat + 8 := by
      simpa using h80
    rw [h80']
    omega
  have hresult12 : (frame + 8) + 4 = frame + 12 := by
    rw [UInt32.add_assoc]
    rw [show (8 : UInt32) + 4 = 12 by decide]
  have hnextInvariant := hinvariant.takeCanonicalDigit
  have hnextMachine :
      acc * UInt64.ofNat 10 + UInt64.ofNat (byte - 48).toNat =
        machineNextAccumulator acc c := by
    rw [hdecode]
    rfl
  iintro ⟨Hruntime, Hglobal, Hinner4, Hinner8, Hinner12,
    Hresult8, Hresult12, Hcopy56, Hcopy60, Hacc, Hpointer, Hlength,
    Hcont⟩
  simp only [decimalDigitCallSegment, List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 8 frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hresult12' : pointsTo_u32 ((frame + 8) + 4) oldResult12 $$
      [Hresult12]
  · rw [hresult12]
    iexact Hresult12
  have Hparse := parseByte_call_twp (α := α)
    (frame + 8) byte 10 frame
    oldInner4 oldInner8 oldInner12 oldResult8 oldResult12
    (by decide) (by decide) hbyteNumeric hdigit hinnerRoom hresultRoom
    (callerLocals :=
      ⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
        decimalDigitLocals frame currentPtr currentLength
          nextPtr nextLength byte oldTemporary oldFinal, []⟩)
    (stack := []) (code := decimalDigitCallSegment.drop 6 ++ code)
    (arity := arity) (remainder := remainder)
    (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [decimalDigitCallSegment, List.drop, List.append_nil,
    List.cons_append, List.nil_append] at Hparse
  iapply Hparse
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinner4]
  · iexact Hinner4
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hresult8]
  · iexact Hresult8
  isplitl [Hresult12']
  · iexact Hresult12'
  iintro Hpost
  icases Hpost with ⟨Hruntime, Hglobal, Hinner4, Hinner8, Hinner12,
    Hresult8, Hresult12'⟩
  ihave Hresult12 : pointsTo_u32 (frame + 12) (byte - 48) $$
      [Hresult12']
  · rw [← hresult12]
    iexact Hresult12'
  iapply twp_localGet rfl
  iapply twp_load32 (byte - 48) h120 h121 h122 h123 $$ Hresult12
  iintro Hresult12
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 1 h80 h81 h82 h83 $$ Hresult8
  iintro Hresult8
  iapply twp_store32 oldCopy56 h560 h561 h562 h563 $$ Hcopy56
  iintro Hcopy56
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldCopy60 h600 h601 h602 h603 $$ Hcopy60
  iintro Hcopy60
  iapply twp_block
  simp only [decimalDigitResultBody]
  iapply twp_localGet rfl
  iapply twp_load32 1 h560 h561 h562 h563 $$ Hcopy56
  iintro Hcopy56
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_eqz (result := 0) (by decide)
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_load32 (byte - 48) h600 h601 h602 h603 $$ Hcopy60
  iintro Hcopy60
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64
    (acc * UInt64.ofNat 10) h1120 h1121 h1122 h1123 h1124 h1125
      h1126 h1127 $$ Hacc
  iintro Hacc
  iapply twp_localGet rfl
  iapply twp_extendUI32
  iapply twp_addI64
  rw [hnextMachine]
  iapply Wasm.SmallStep.twp_store64
    (acc * UInt64.ofNat 10) h1120 h1121 h1122 h1123 h1124 h1125
      h1126 h1127 $$ Hacc
  iintro Hacc
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldPointer h480 h481 h482 h483 $$ Hpointer
  iintro Hpointer
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldLength h520 h521 h522 h523 $$ Hlength
  iintro Hlength
  simp only [fromAsciiRadixParams, decimalDigitLocals,
    fromAsciiRadixFramedLocals, fromAsciiRadixZeroLocals, func51Def,
    List.map_cons, List.map_nil, ValueType.zero, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set,
    List.drop_zero]
  iapply Hcont
  isplit
  · ipureintro
    exact hnextInvariant
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinner4]
  · iexact Hinner4
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hresult8]
  · iexact Hresult8
  isplitl [Hresult12]
  · iexact Hresult12
  isplitl [Hcopy56]
  · iexact Hcopy56
  isplitl [Hcopy60]
  · iexact Hcopy60
  isplitl [Hacc]
  · iexact Hacc
  isplitl [Hpointer]
  · iexact Hpointer
  iexact Hlength

set_option maxHeartbeats 2000000 in
/-- Exact nonempty iteration and backedge of the generated simple decimal
loop.  The recursive continuation is exposed only after the canonical
remaining-length measure has strictly decreased. -/
theorem decimalSimpleLoop_backedge_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame currentPtr currentLength : UInt32)
    (value acc : UInt64) (consumed rest : List Char) (c : Char)
    (oldCurrentPtr oldCurrentLength oldNextPtr oldNextLength : UInt32)
    (oldByte oldTemporary oldFinal : UInt32)
    (oldInner4 oldInner8 oldInner12 : UInt32)
    (oldResult8 oldResult12 oldCopy56 oldCopy60 : UInt32)
    (hinnerRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hframeRoom : frame.toNat + 120 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    let loopFrame : ControlFrame :=
      { kind := .loop
        paramArity := 0
        resultArity := 0
        body := decimalSimpleLoopBody
        continuation := code
        belowStack := [] }
    ⌜DecimalMachineLoopInvariant
        (toString value) consumed (c :: rest) acc⌝ ∗
      runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      (currentPtr ↦w (UInt8.ofNat c.toNat)) ∗
      pointsTo_u32 ((frame - 16) + 4) oldInner4 ∗
      pointsTo_u32 ((frame - 16) + 8) oldInner8 ∗
      pointsTo_u32 ((frame - 16) + 12) oldInner12 ∗
      pointsTo_u32 (frame + 8) oldResult8 ∗
      pointsTo_u32 (frame + 12) oldResult12 ∗
      pointsTo_u32 (frame + 56) oldCopy56 ∗
      pointsTo_u32 (frame + 60) oldCopy60 ∗
      pointsTo_u64 (frame + 112) acc ∗
      pointsTo_u32 (frame + 48) currentPtr ∗
      pointsTo_u32 (frame + 52) currentLength ∗
      ((⌜rest.length < (c :: rest).length⌝ ∗
        ⌜DecimalMachineLoopInvariant (toString value)
          (consumed ++ [c]) rest (machineNextAccumulator acc c)⌝ ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 frame) ∗
        (currentPtr + 0 ↦w (UInt8.ofNat c.toNat)) ∗
        pointsTo_u32 ((frame - 16) + 4) 1 ∗
        pointsTo_u32 ((frame - 16) + 8) (asciiByte32 c - 48) ∗
        pointsTo_u32 ((frame - 16) + 12) (asciiByte32 c - 48) ∗
        pointsTo_u32 (frame + 8) 1 ∗
        pointsTo_u32 (frame + 12) (asciiByte32 c - 48) ∗
        pointsTo_u32 (frame + 56) 1 ∗
        pointsTo_u32 (frame + 60) (asciiByte32 c - 48) ∗
        pointsTo_u64 (frame + 112) (machineNextAccumulator acc c) ∗
        pointsTo_u32 (frame + 48) (1 + currentPtr) ∗
        pointsTo_u32 (frame + 52) (currentLength - 1)) -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              decimalDigitLocals frame currentPtr currentLength
                (1 + currentPtr) (currentLength - 1) (asciiByte32 c)
                (asciiByte32 c - 48) (asciiByte32 c - 48), []⟩,
            decimalSimpleLoopBody, arity, remainder,
            loopFrame :: controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          decimalDigitLocals frame oldCurrentPtr oldCurrentLength
            oldNextPtr oldNextLength oldByte oldTemporary oldFinal, []⟩,
        decimalSimpleLoopAfterGuard, arity, remainder,
        loopFrame :: controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  dsimp only
  obtain ⟨h480, h481, h482, h483⟩ :=
    parserWideSlotFacts frame 48 hframeRoom (by decide)
  obtain ⟨h520, h521, h522, h523⟩ :=
    parserWideSlotFacts frame 52 hframeRoom (by decide)
  iintro ⟨%hinvariant, Hruntime, Hglobal, Hbyte,
    Hinner4, Hinner8, Hinner12, Hresult8, Hresult12,
    Hcopy56, Hcopy60, Hacc, Hpointer, Hlength, Hrec⟩
  simp only [decimalSimpleLoopAfterGuard, List.cons_append, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 currentPtr h480 h481 h482 h483 $$ Hpointer
  iintro Hpointer
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 currentPtr h480 h481 h482 h483 $$ Hpointer
  iintro Hpointer
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_load32 currentLength h520 h521 h522 h523 $$ Hlength
  iintro Hlength
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [fromAsciiRadixParams, decimalDigitLocals,
    fromAsciiRadixFramedLocals, fromAsciiRadixZeroLocals, func51Def,
    List.map_cons, List.map_nil, ValueType.zero, List.length_cons,
    List.length_nil, Nat.reduceAdd, Nat.reduceSub, List.set]
  have Hprepare := decimalDigitPrepareSegment_twp (α := α)
    resultPtr textPtr textLength frame currentPtr currentLength
    (1 + currentPtr) (currentLength - 1) value acc consumed rest c
    oldByte oldTemporary oldFinal hinvariant hframeRoom
    (code := []) (arity := arity) (remainder := remainder)
    (controls :=
      { kind := .loop, paramArity := 0, resultArity := 0
        body := decimalSimpleLoopBody, continuation := code
        belowStack := [] } :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil] at Hprepare
  simp only [fromAsciiRadixParams, decimalDigitLocals,
    fromAsciiRadixFramedLocals, fromAsciiRadixZeroLocals, func51Def,
    List.map_cons, List.map_nil, ValueType.zero, List.set] at Hprepare
  iapply Hprepare
  isplitl [Hacc]
  · iexact Hacc
  isplitl [Hbyte]
  · iexact Hbyte
  iintro Hacc Hbyte
  have hbyteFacts := canonicalDigitByteFacts hinvariant
  have Hcall := decimalDigitCallSegment_twp (α := α)
    resultPtr textPtr textLength frame currentPtr currentLength
    (1 + currentPtr) (currentLength - 1) (asciiByte32 c)
    value acc consumed rest c oldTemporary oldFinal
    oldInner4 oldInner8 oldInner12 oldResult8 oldResult12
    oldCopy56 oldCopy60 currentPtr currentLength
    hbyteFacts.1 hbyteFacts.2.1 hbyteFacts.2.2 hinvariant
    hinnerRoom hframeRoom
    (code := []) (arity := arity) (remainder := remainder)
    (controls :=
      { kind := .loop, paramArity := 0, resultArity := 0
        body := decimalSimpleLoopBody, continuation := code
        belowStack := [] } :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [List.append_nil] at Hcall
  simp only [fromAsciiRadixParams, decimalDigitLocals,
    fromAsciiRadixFramedLocals, fromAsciiRadixZeroLocals, func51Def,
    List.map_cons, List.map_nil, ValueType.zero, List.set] at Hcall
  iapply Hcall
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinner4]
  · iexact Hinner4
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hresult8]
  · iexact Hresult8
  isplitl [Hresult12]
  · iexact Hresult12
  isplitl [Hcopy56]
  · iexact Hcopy56
  isplitl [Hcopy60]
  · iexact Hcopy60
  isplitl [Hacc]
  · iexact Hacc
  isplitl [Hpointer]
  · iexact Hpointer
  isplitl [Hlength]
  · iexact Hlength
  iintro Hpost
  icases Hpost with ⟨%hnextInvariant, Hruntime, Hglobal,
    Hinner4, Hinner8, Hinner12, Hresult8, Hresult12,
    Hcopy56, Hcopy60, Hacc, Hpointer, Hlength⟩
  iapply twp_br rfl
  simp only [List.take_zero, List.nil_append]
  iapply Hrec
  isplit
  · ipureintro
    simp
  isplit
  · ipureintro
    exact hnextInvariant
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hbyte]
  · iexact Hbyte
  isplitl [Hinner4]
  · iexact Hinner4
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hresult8]
  · iexact Hresult8
  isplitl [Hresult12]
  · iexact Hresult12
  isplitl [Hcopy56]
  · iexact Hcopy56
  isplitl [Hcopy60]
  · iexact Hcopy60
  isplitl [Hacc]
  · iexact Hacc
  isplitl [Hpointer]
  · iexact Hpointer
  iexact Hlength

/-- Empty-remaining branch of the exact generated simple-loop guard.  The
depth-three target is supplied explicitly because it belongs to `func51`'s
surrounding nested blocks, not to the loop itself. -/
theorem decimalSimpleLoop_empty_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame : UInt32)
    (localValues : List Value)
    (hframeLocal :
      (⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          localValues, []⟩ : Locals).get 4 = some (.i32 frame))
    (hframeRoom : frame.toNat + 120 ≤ UInt32.size)
    {code targetCode : Program} {arity : Nat}
    {remainder targetValues : List Value}
    {controls targetControls : List ControlFrame}
    {calls : List CallFrame}
    (htarget : branchTarget? arity 3
      ({ kind := .loop
         paramArity := 0
         resultArity := 0
         body := decimalSimpleLoopBody
         continuation := code
         belowStack := [] } :: controls) [] =
      some (targetCode, targetControls, targetValues)) :
    pointsTo_u32 (frame + 52) 0 ∗
      (pointsTo_u32 (frame + 52) 0 -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              localValues, targetValues⟩,
            targetCode, arity, remainder, targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          localValues, []⟩,
        decimalSimpleLoopBody, arity, remainder,
        { kind := .loop
          paramArity := 0
          resultArity := 0
          body := decimalSimpleLoopBody
          continuation := code
          belowStack := [] } :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h520, h521, h522, h523⟩ :=
    parserWideSlotFacts frame 52 hframeRoom (by decide)
  iintro ⟨Hlength, Hfinish⟩
  simp only [decimalSimpleLoopBody, List.cons_append, List.nil_append]
  iapply twp_localGet hframeLocal
  iapply twp_load32 0 h520 h521 h522 h523 $$ Hlength
  iintro Hlength
  iapply twp_const
  iapply twp_geU (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  have Hbranch := twp_brIf (α := α) (s := s) (E := E) (Φ := Φ)
    (params := fromAsciiRadixParams resultPtr textPtr textLength 10)
    (localValues := localValues) (values := []) (condition := 1)
    (depth := 3) (arity := arity) (code := decimalSimpleLoopAfterGuard)
    (targetCode := targetCode) (remainder := remainder)
    (controls :=
      { kind := .loop, paramArity := 0, resultArity := 0
        body := decimalSimpleLoopBody, continuation := code
        belowStack := [] } :: controls)
    (targetControl := targetControls) (targetValues := targetValues)
    (calls := calls) (by decide) htarget
  simp only [decimalSimpleLoopBody, List.cons_append, List.nil_append] at Hbranch
  iapply Hbranch
  iapply Hfinish $$ Hlength

/-- Total well-founded wrapper for the exact generated simple decimal loop.
The nonempty premise is designed to be discharged by
`decimalSimpleLoop_backedge_twp`; the empty premise is discharged by
`decimalSimpleLoop_empty_twp`. -/
theorem decimalSimpleLoop_wf
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (locals : List Char → Locals)
    (I : List Char → IProp WasmHeapGF)
    (initial : List Char)
    {code : Program} {arity : Nat} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbelow : belowStack = (locals initial).values.drop 0)
    (empty_closes :
      ⊢@{IProp WasmHeapGF} (iprop%
        I [] -∗
          WP (loopBodyExpr (α := α) (locals []) 0 0 arity
            decimalSimpleLoopBody code remainder belowStack controls calls)
          @ s; E [{ Φ }]))
    (nonempty_closes : ∀ c rest,
      ⊢@{IProp WasmHeapGF} (iprop%
        (I rest -∗
          WP (loopBodyExpr (α := α) (locals rest) 0 0 arity
            decimalSimpleLoopBody code remainder belowStack controls calls)
          @ s; E [{ Φ }]) -∗
        I (c :: rest) -∗
          WP (loopBodyExpr (α := α) (locals (c :: rest)) 0 0 arity
            decimalSimpleLoopBody code remainder belowStack controls calls)
          @ s; E [{ Φ }])) :
    I initial ⊢
      WP (.running
        ⟨locals initial,
          .loop 0 0 decimalSimpleLoopBody :: code,
          arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iapply Wasm.SmallStep.twp_loop_wf_family
    (measure := fun remaining : List Char => remaining.length)
    (locals := locals) (I := I) (initial := initial)
    (initialLocals := locals initial)
    (paramArity := 0) (resultArity := 0)
    (body := decimalSimpleLoopBody) (code := code)
    (belowStack := belowStack) rfl hbelow
  · intro remaining
    cases remaining with
    | nil =>
        iintro _ Hinv
        iapply empty_closes
        iexact Hinv
    | cons c rest =>
        iintro Hrec Hinv
        ispecialize Hrec $$ %rest
        ihave Hnext :
            (I rest -∗
              WP (loopBodyExpr (α := α) (locals rest) 0 0 arity
                decimalSimpleLoopBody code remainder belowStack
                controls calls) @ s; E [{ Φ }]) $$ [Hrec]
        · iintro Hrest
          iapply Hrec
          · ipureintro
            simp
          · iexact Hrest
        iapply nonempty_closes c rest $$ Hnext Hinv

/-! ## Exact generated checked decimal loop

The generated parser contains a second digit loop for inputs longer than
sixteen characters.  Each iteration widens the accumulator, multiplies by the
radix through the absolute-index-`256` 128-bit multiply, and adds the decoded
digit through a checked add.  On canonical `UInt64` renderings both overflow
probes are statically false (`mulAcc_bound`, `canonicalDigit_no_add_overflow`).
-/

/-- Innermost checked block: the wide-multiply overflow probe and the
successful decoder path of one checked iteration. -/
def decimalCheckedDecodeBody : Program := [
  .localGet 21, .const 1, .and, .br_if 0,
  .localGet 4, .localGet 22, .store64 72,
  .localGet 4, .constI64 1, .store64 64,
  .localGet 4, .localGet 13, .load8U 0, .store8 103,
  .localGet 4, .localGet 4, .load8U 103, .const 255, .and, .store32 96,
  .localGet 4, .load32 96, .localSet 23,
  .localGet 4, .const 24, .add, .localGet 23, .localGet 3, .call 54,
  .localGet 4, .load32 28, .localSet 24,
  .localGet 4, .localGet 4, .load32 24, .store32 88,
  .localGet 4, .localGet 24, .store32 92,
  .localGet 4, .localGet 4, .load32 88, .store32 104,
  .localGet 4, .load32 104, .const 1, .and, .br_if 1,
  .br 2]

/-- Multiply-overflow decoder path of the checked loop.  Unreachable on
canonical tokens. -/
def decimalCheckedOverflowBody : Program := [
  .const 0, .load64 1049104, .localSet 25,
  .const 0, .load64 1049112, .localSet 26,
  .localGet 4, .localGet 25, .store64 64,
  .localGet 4, .localGet 26, .store64 72,
  .localGet 4, .localGet 13, .load8U 0, .store8 103,
  .localGet 4, .localGet 4, .load8U 103, .const 255, .and, .store32 96,
  .localGet 4, .load32 96, .localSet 27,
  .localGet 4, .const 16, .add, .localGet 27, .localGet 3, .call 54,
  .localGet 4, .load32 20, .localSet 28,
  .localGet 4, .localGet 4, .load32 16, .store32 88,
  .localGet 4, .localGet 28, .store32 92,
  .localGet 4, .localGet 4, .load32 88, .store32 104,
  .localGet 4, .load32 104, .const 1, .and, .br_if 5,
  .br 1]

/-- Checked-add segment entered after a successful digit decode. -/
def decimalCheckedAddBody : Program := [
  .localGet 4, .localGet 4, .load32 92, .store32 108,
  .localGet 4, .localGet 4, .load32 108, .extendUI32, .store64 80,
  .localGet 4, .localGet 4, .load64 72, .store64 112,
  .localGet 4, .load64 112, .localSet 29,
  .localGet 29, .localGet 4, .load64 80, .addI64,
  .localGet 29, .ltUI64, .const 1, .and, .br_if 2,
  .br 1]

/-- Invalid-digit error writer of the checked loop.  Unreachable on canonical
tokens. -/
def decimalCheckedFailBody : Program := [
  .localGet 0, .const 1, .store8 1,
  .localGet 0, .const 1, .store8 0, .br 5]

/-- Commit tail of one checked iteration: store the checked sum and advance
the pointer/length pair, then take the loop back-edge. -/
def decimalCheckedCommitBody : Program := [
  .localGet 4, .localGet 4, .load64 112,
  .localGet 4, .load64 80, .addI64, .store64 128,
  .localGet 4, .constI64 1, .store64 120,
  .localGet 4, .localGet 4, .load64 128, .store64 112,
  .localGet 4, .localGet 16, .store32 48,
  .localGet 4, .localGet 17, .store32 52,
  .br 1]

/-- The five nested result blocks of one checked iteration. -/
def decimalCheckedBlockBody : Program :=
  .block 0 0
      (.block 0 0
          (.block 0 0
              (.block 0 0 decimalCheckedDecodeBody ::
                decimalCheckedOverflowBody) ::
            decimalCheckedAddBody) ::
        decimalCheckedFailBody) ::
    decimalCheckedCommitBody

/-- Post-multiply tail of one checked iteration, beginning immediately after
the absolute-index-`256` wide-multiply call. -/
def decimalCheckedTail : Program := [
  .localGet 20, .localGet 4, .load64 40, .neI64, .localSet 21,
  .localGet 4, .load64 32, .localSet 22,
  .block 0 0 decimalCheckedBlockBody]

/-- Exact generated segment crossing the wide-multiply call. -/
def decimalCheckedCallSegment : Program := .call 256 :: decimalCheckedTail

/-- Generated prefix of one checked iteration: latch pointer, length, radix,
and the accumulator into locals and stage the wide-multiply operands. -/
def decimalCheckedPrepareSegment : Program := [
  .localGet 4, .load32 48, .localSet 13,
  .localGet 4, .load32 48, .localSet 14,
  .localGet 4, .load32 52, .localSet 15,
  .localGet 14, .const 1, .add, .localSet 16,
  .localGet 15, .const 1, .sub, .localSet 17,
  .localGet 3, .extendUI32, .localSet 18,
  .localGet 4, .load64 112, .localSet 19,
  .constI64 0, .localSet 20,
  .localGet 4, .const 32, .add,
  .localGet 19, .localGet 20, .localGet 18, .localGet 20]

/-- Nonempty portion of the generated checked decimal loop, beginning just
after its length guard. -/
def decimalCheckedLoopAfterGuard : Program :=
  decimalCheckedPrepareSegment ++ decimalCheckedCallSegment

def decimalCheckedLoopBody : Program := [
  .localGet 4, .load32 52, .const 1, .geU,
  .const 1, .and, .eqz, .br_if 5] ++ decimalCheckedLoopAfterGuard

/-! ## Anchor: the transcribed loops inside generated `func51`

The block skeleton below rebuilds `fromAsciiRadixAfterRadixCheck` from the
named loop bodies, so a single `rfl` pins every transcription (including
`decimalSimpleLoopBody`) to the generated program. -/

/-- Empty-input error block. -/
def parserEmptyCheckBody : Program := [
  .localGet 5, .br_if 0,
  .localGet 0, .const 0, .store8 1,
  .localGet 0, .const 1, .store8 0, .br 1]

/-- Single-character sign probe with its branch table. -/
def parserSignProbeBody : Program := [
  .localGet 5, .const 1, .eq, .const 1, .and, .eqz, .br_if 0,
  .localGet 4, .load32 48, .load8U 0,
  .const 4294967253, .add, .const 255, .and, .localSet 6,
  .localGet 6, .const 2, .gtU, .drop,
  .localGet 6, .brTable [1, 0, 1] 0]

/-- Sign-consumption block for signed multi-character inputs. -/
def parserSignConsumeBody : Program :=
  .block 0 0 [.localGet 7, .brTable [0, 2, 1] 2] :: [
  .localGet 4, .load32 48, .localSet 8,
  .localGet 4, .load32 52, .localSet 9,
  .localGet 8, .const 1, .add, .localSet 10,
  .localGet 9, .const 1, .sub, .localSet 11,
  .localGet 4, .const 1, .store8 143,
  .localGet 4, .localGet 10, .store32 48,
  .localGet 4, .localGet 11, .store32 52,
  .br 2]

/-- First-byte scan of the nonempty input. -/
def parserSignScanBody : Program :=
  .block 0 0
      (.block 0 0
          (.block 0 0 parserSignProbeBody :: [
            .localGet 5, .const 1, .geU, .const 1, .and, .br_if 1,
            .br 2]) :: [
        .localGet 0, .const 1, .store8 1,
        .localGet 0, .const 1, .store8 0, .br 3]) :: [
  .localGet 4, .load32 48, .load8U 0,
  .const 4294967253, .add, .const 255, .and, .localSet 7,
  .localGet 7, .const 2, .gtU, .drop,
  .block 0 0 parserSignConsumeBody]

/-- Complete sign/empty dispatch region. -/
def parserSignBody : Program :=
  .block 0 0 parserSignScanBody :: [
  .localGet 4, .const 1, .store8 143]

/-- Loop selection: radix and length both at most sixteen choose the simple
loop, otherwise the checked loop runs. -/
def parserLoopChoiceBody : Program :=
  .block 0 0
      (.block 0 0
          (.block 0 0
              (.block 0 0
                  (.block 0 0
                      (.block 0 0
                          (.block 0 0 [
                            .localGet 3, .const 16, .leU,
                            .const 1, .and, .br_if 0, .br 1] :: [
                            .localGet 12, .const 16, .leU,
                            .const 1, .and, .br_if 1]) :: [.br 1]) ::
                    [.br 1]) :: [
                .block 0 0
                  (.loop 0 0 decimalCheckedLoopBody :: [
                    .localGet 0, .const 2, .store8 1,
                    .localGet 0, .const 1, .store8 0, .br 2]),
                .localGet 4, .localGet 4, .load32 92, .store32 108,
                .localGet 4, .localGet 4, .load32 108,
                .extendUI32, .store64 80,
                .localGet 0, .const 2, .store8 1,
                .localGet 0, .const 1, .store8 0, .br 1]) ::
            .loop 0 0 decimalSimpleLoopBody :: [
            .localGet 0, .const 1, .store8 1,
            .localGet 0, .const 1, .store8 0, .br 1]) ::
        []) :: [.br 1]

/-- Everything between the radix validation and the frame epilogue. -/
def parserMainBody : Program := [
  .block 0 0 parserEmptyCheckBody,
  .block 0 0 parserSignBody,
  .localGet 4, .constI64 0, .store64 112,
  .localGet 4, .load32 52, .localSet 12,
  .block 0 0 parserLoopChoiceBody,
  .localGet 0, .localGet 4, .load64 112, .store64 8,
  .localGet 0, .const 0, .store8 0]

/-- The transcribed loop bodies sit at exactly these positions of the
generated function. -/
theorem fromAsciiRadixAfterRadixCheck_eq :
    fromAsciiRadixAfterRadixCheck = [
      .localGet 4, .load32 52, .localSet 5,
      .block 0 0 parserMainBody,
      .localGet 4, .const 144, .add, .globalSet 0, .ret] := rfl

/-! ## Machine rules for the checked loop -/

private theorem parserSlotFactsAt (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 4 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 3) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega)⟩

private theorem parserSlot64FactsAt (base : UInt32) (offset total : Nat)
    (hroom : base.toNat + total ≤ UInt32.size)
    (hoffset : offset + 8 ≤ total) :
    (base + UInt32.ofNat offset).toNat = base.toNat + offset ∧
    ((base + UInt32.ofNat offset) + 1).toNat =
      (base + UInt32.ofNat offset).toNat + 1 ∧
    ((base + UInt32.ofNat offset) + 2).toNat =
      (base + UInt32.ofNat offset).toNat + 2 ∧
    ((base + UInt32.ofNat offset) + 3).toNat =
      (base + UInt32.ofNat offset).toNat + 3 ∧
    ((base + UInt32.ofNat offset) + 4).toNat =
      (base + UInt32.ofNat offset).toNat + 4 ∧
    ((base + UInt32.ofNat offset) + 5).toNat =
      (base + UInt32.ofNat offset).toNat + 5 ∧
    ((base + UInt32.ofNat offset) + 6).toNat =
      (base + UInt32.ofNat offset).toNat + 6 ∧
    ((base + UInt32.ofNat offset) + 7).toNat =
      (base + UInt32.ofNat offset).toNat + 7 := by
  have hoff : offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have hbaseOffset : base.toNat + offset < UInt32.size := by
    simp only [UInt32.size] at hroom ⊢
    omega
  have h0 := UInt32.add_ofNat_toNat_noWrap base offset hoff hbaseOffset
  have hstep (n : Nat) (hn : n ≤ 7) :
      ((base + UInt32.ofNat offset) + UInt32.ofNat n).toNat =
        (base + UInt32.ofNat offset).toNat + n := by
    apply UInt32.add_ofNat_toNat_noWrap
    · omega
    · rw [h0]
      simp only [UInt32.size] at hroom ⊢
      omega
  exact ⟨h0, by simpa using hstep 1 (by omega),
    by simpa using hstep 2 (by omega), by simpa using hstep 3 (by omega),
    by simpa using hstep 4 (by omega), by simpa using hstep 5 (by omega),
    by simpa using hstep 6 (by omega), by simpa using hstep 7 (by omega)⟩

private theorem twp_neI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {lhs rhs : UInt64} {result : UInt32} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame}
    (hresult : result = if lhs ≠ rhs then 1 else 0) :
    WP (.running
      ⟨⟨params, localValues, .i32 result :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, .i64 rhs :: .i64 lhs :: values⟩,
        .neI64 :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.neI64 hresult)

private theorem twp_constI64
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    {params localValues values : List Value}
    {v : UInt64} {code : Program} {arity : Nat}
    {remainder : List Value} {controls : List ControlFrame}
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨params, localValues, .i64 v :: values⟩,
        code, arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨params, localValues, values⟩,
        .constI64 v :: code, arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] :=
  twp_pureStep _ _ _ (fun _ => Step.constI64)

private theorem asciiByte32_toUInt8 (c : Char) :
    (asciiByte32 c).toUInt8 = UInt8.ofNat c.toNat := by
  simp [asciiByte32]

/-- Locals of generated `func51` inside the checked decimal loop, written as
a literal list because `Locals.get` reduction is exponential in the depth of
a `List.set` chain.  Slot `n` holds generated local `n + 4`; the dispatch
scratch locals `5`, `6`, `7`, and `12` are kept abstract so the rule composes
with the sign/empty dispatch, and the sign-consumption locals `8`--`11` are
zero on the unsigned path. -/
def decimalCheckedLocals
    (frame l5 l6 l7 l12 l13 l14 l15 l16 l17 : UInt32)
    (l18 l19 l20 : UInt64) (l21 : UInt32) (l22 : UInt64)
    (l23 l24 : UInt32) (l25 l26 : UInt64) (l27 l28 : UInt32)
    (l29 : UInt64) : List Value :=
  [.i32 frame, .i32 l5, .i32 l6, .i32 l7,
   .i32 0, .i32 0, .i32 0, .i32 0,
   .i32 l12, .i32 l13, .i32 l14, .i32 l15, .i32 l16, .i32 l17,
   .i64 l18, .i64 l19, .i64 l20, .i32 l21, .i64 l22,
   .i32 l23, .i32 l24, .i64 l25, .i64 l26, .i32 l27, .i32 l28,
   .i64 l29,
   .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0, .i32 0]

theorem decimalCheckedLocals_zero :
    decimalCheckedLocals 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 =
      fromAsciiRadixZeroLocals.set 0 (.i32 0) := rfl

set_option maxHeartbeats 1000000 in
/-- Exact preparation prefix of one checked iteration: latch the current
pointer/length pair, the widened radix, and the accumulator into locals, and
stage the operand stack of the absolute-index-`256` wide multiply. -/
theorem decimalCheckedPrepareSegment_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame : UInt32)
    (currentPtr currentLength : UInt32) (acc : UInt64)
    (l5 l6 l7 l12 l13 l14 l15 l16 l17 : UInt32) (l18 l19 l20 : UInt64)
    (l21 : UInt32) (l22 : UInt64) (l23 l24 : UInt32)
    (l25 l26 : UInt64) (l27 l28 : UInt32) (l29 : UInt64)
    (hframeRoom : frame.toNat + 136 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    pointsTo_u32 (frame + 48) currentPtr ∗
      pointsTo_u32 (frame + 52) currentLength ∗
      pointsTo_u64 (frame + 112) acc ∗
      (pointsTo_u32 (frame + 48) currentPtr -∗
        pointsTo_u32 (frame + 52) currentLength -∗
        pointsTo_u64 (frame + 112) acc -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              decimalCheckedLocals frame l5 l6 l7 l12 currentPtr
                currentPtr currentLength (1 + currentPtr)
                (currentLength - 1) 10 acc 0
                l21 l22 l23 l24 l25 l26 l27 l28 l29,
              [.i64 0, .i64 10, .i64 0, .i64 acc, .i32 (frame + 32)]⟩,
            decimalCheckedCallSegment ++ code,
            arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          decimalCheckedLocals frame l5 l6 l7 l12 l13 l14 l15 l16 l17
            l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29, []⟩,
        decimalCheckedPrepareSegment ++ decimalCheckedCallSegment ++ code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h480, h481, h482, h483⟩ :=
    parserSlotFactsAt frame 48 136 hframeRoom (by omega)
  obtain ⟨h520, h521, h522, h523⟩ :=
    parserSlotFactsAt frame 52 136 hframeRoom (by omega)
  obtain ⟨h1120, h1121, h1122, h1123, h1124, h1125, h1126, h1127⟩ :=
    parserSlot64FactsAt frame 112 136 hframeRoom (by omega)
  iintro ⟨Hptr, Hlen, Hacc, Hcont⟩
  simp only [decimalCheckedPrepareSegment, List.cons_append,
    List.nil_append]
  iapply twp_localGet rfl
  iapply twp_load32 currentPtr h480 h481 h482 h483 $$ Hptr
  iintro Hptr
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_load32 currentPtr h480 h481 h482 h483 $$ Hptr
  iintro Hptr
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_load32 currentLength h520 h521 h522 h523 $$ Hlen
  iintro Hlen
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_extendUI32
  rw [show UInt64.ofNat ((10 : UInt32)).toNat = (10 : UInt64) by decide]
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 acc h1120 h1121 h1122 h1123 h1124
      h1125 h1126 h1127 $$ Hacc
  iintro Hacc
  iapply twp_localSet rfl
  simp only []
  iapply twp_constI64
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 32 frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [fromAsciiRadixParams, decimalCheckedLocals,
    List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceSub,
    List.set]
  iapply Hcont $$ Hptr Hlen Hacc

set_option maxHeartbeats 24000000 in
/-- One exact successful canonical-digit segment of the checked loop in
generated `func51`.

Starting from the operand stack staged by the prepare segment, this rule
crosses the absolute-index-`256` wide multiply, refutes its overflow probe,
crosses the absolute-index-`54` decoder, takes the successful block path,
refutes the checked-add probe, and commits the next accumulator, pointer,
and length.  It stops at the loop back-edge. -/
theorem decimalCheckedCallSegment_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame : UInt32)
    (currentPtr currentLength : UInt32)
    (value acc : UInt64) (consumed rest : List Char) (c : Char)
    (l5 l6 l7 l12 : UInt32)
    (l21 : UInt32) (l22 : UInt64) (l23 l24 : UInt32)
    (l25 l26 : UInt64) (l27 l28 : UInt32) (l29 : UInt64)
    (oldWideLow oldWideHigh : UInt64)
    (oldInner4 oldInner8 oldInner12 : UInt32)
    (oldResult24 oldResult28 : UInt32)
    (old64 old72 old80 : UInt64)
    (old88 old92 old96 : UInt32) (oldByte103 : UInt8)
    (old104 old108 : UInt32)
    (old120 old128 : UInt64)
    (oldPointer oldLength : UInt32)
    (hinvariant : DecimalMachineLoopInvariant
      (toString value) consumed (c :: rest) acc)
    (hinnerRoom : (frame - 16).toNat + 16 ≤ UInt32.size)
    (hframeRoom : frame.toNat + 136 ≤ UInt32.size)
    {code : Program} {arity : Nat} {remainder : List Value}
    {controls : List ControlFrame} {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 frame) ∗
      (currentPtr ↦w (UInt8.ofNat c.toNat)) ∗
      pointsTo_u64 (frame + 32) oldWideLow ∗
      pointsTo_u64 (frame + 40) oldWideHigh ∗
      pointsTo_u32 ((frame - 16) + 4) oldInner4 ∗
      pointsTo_u32 ((frame - 16) + 8) oldInner8 ∗
      pointsTo_u32 ((frame - 16) + 12) oldInner12 ∗
      pointsTo_u32 (frame + 24) oldResult24 ∗
      pointsTo_u32 (frame + 28) oldResult28 ∗
      pointsTo_u64 (frame + 64) old64 ∗
      pointsTo_u64 (frame + 72) old72 ∗
      pointsTo_u64 (frame + 80) old80 ∗
      pointsTo_u32 (frame + 88) old88 ∗
      pointsTo_u32 (frame + 92) old92 ∗
      pointsTo_u32 (frame + 96) old96 ∗
      ((frame + 103) ↦w oldByte103) ∗
      pointsTo_u32 (frame + 104) old104 ∗
      pointsTo_u32 (frame + 108) old108 ∗
      pointsTo_u64 (frame + 112) acc ∗
      pointsTo_u64 (frame + 120) old120 ∗
      pointsTo_u64 (frame + 128) old128 ∗
      pointsTo_u32 (frame + 48) oldPointer ∗
      pointsTo_u32 (frame + 52) oldLength ∗
      ((⌜DecimalMachineLoopInvariant (toString value)
          (consumed ++ [c]) rest (machineNextAccumulator acc c)⌝ ∗
        runtimeModuleOwn «module» ∗
        globalPointsTo 0 (.i32 frame) ∗
        (currentPtr + 0 ↦w (UInt8.ofNat c.toNat)) ∗
        pointsTo_u64 (frame + 32) (acc * 10) ∗
        pointsTo_u64 (frame + 40) 0 ∗
        pointsTo_u32 ((frame - 16) + 4) 1 ∗
        pointsTo_u32 ((frame - 16) + 8) (asciiByte32 c - 48) ∗
        pointsTo_u32 ((frame - 16) + 12) (asciiByte32 c - 48) ∗
        pointsTo_u32 (frame + 24) 1 ∗
        pointsTo_u32 (frame + 28) (asciiByte32 c - 48) ∗
        pointsTo_u64 (frame + 64) 1 ∗
        pointsTo_u64 (frame + 72) (acc * 10) ∗
        pointsTo_u64 (frame + 80) (UInt64.ofNat (digitNat c)) ∗
        pointsTo_u32 (frame + 88) 1 ∗
        pointsTo_u32 (frame + 92) (asciiByte32 c - 48) ∗
        pointsTo_u32 (frame + 96) (asciiByte32 c) ∗
        ((frame + 103) ↦w (UInt8.ofNat c.toNat)) ∗
        pointsTo_u32 (frame + 104) 1 ∗
        pointsTo_u32 (frame + 108) (asciiByte32 c - 48) ∗
        pointsTo_u64 (frame + 112) (machineNextAccumulator acc c) ∗
        pointsTo_u64 (frame + 120) 1 ∗
        pointsTo_u64 (frame + 128) (machineNextAccumulator acc c) ∗
        pointsTo_u32 (frame + 48) (1 + currentPtr) ∗
        pointsTo_u32 (frame + 52) (currentLength - 1)) -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              decimalCheckedLocals frame l5 l6 l7 l12 currentPtr
                currentPtr currentLength (1 + currentPtr)
                (currentLength - 1) 10 acc 0 0 (acc * 10)
                (asciiByte32 c) (asciiByte32 c - 48)
                l25 l26 l27 l28 (acc * 10), []⟩,
            [.br 1], arity, remainder,
            { kind := .block
              paramArity := 0
              resultArity := 0
              body := decimalCheckedBlockBody
              continuation := code
              belowStack := [] } :: controls,
            calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          decimalCheckedLocals frame l5 l6 l7 l12 currentPtr
            currentPtr currentLength (1 + currentPtr)
            (currentLength - 1) 10 acc 0
            l21 l22 l23 l24 l25 l26 l27 l28 l29,
          [.i64 0, .i64 10, .i64 0, .i64 acc, .i32 (frame + 32)]⟩,
        decimalCheckedCallSegment ++ code,
        arity, remainder, controls, calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h320, h321, h322, h323, h324, h325, h326, h327⟩ :=
    parserSlot64FactsAt frame 32 136 hframeRoom (by omega)
  obtain ⟨h400, h401, h402, h403, h404, h405, h406, h407⟩ :=
    parserSlot64FactsAt frame 40 136 hframeRoom (by omega)
  obtain ⟨h640, h641, h642, h643, h644, h645, h646, h647⟩ :=
    parserSlot64FactsAt frame 64 136 hframeRoom (by omega)
  obtain ⟨h720, h721, h722, h723, h724, h725, h726, h727⟩ :=
    parserSlot64FactsAt frame 72 136 hframeRoom (by omega)
  obtain ⟨h800, h801, h802, h803, h804, h805, h806, h807⟩ :=
    parserSlot64FactsAt frame 80 136 hframeRoom (by omega)
  obtain ⟨h1120, h1121, h1122, h1123, h1124, h1125, h1126, h1127⟩ :=
    parserSlot64FactsAt frame 112 136 hframeRoom (by omega)
  obtain ⟨h1200, h1201, h1202, h1203, h1204, h1205, h1206, h1207⟩ :=
    parserSlot64FactsAt frame 120 136 hframeRoom (by omega)
  obtain ⟨h1280, h1281, h1282, h1283, h1284, h1285, h1286, h1287⟩ :=
    parserSlot64FactsAt frame 128 136 hframeRoom (by omega)
  obtain ⟨h240, h241, h242, h243⟩ :=
    parserSlotFactsAt frame 24 136 hframeRoom (by omega)
  obtain ⟨h280, h281, h282, h283⟩ :=
    parserSlotFactsAt frame 28 136 hframeRoom (by omega)
  obtain ⟨h480, h481, h482, h483⟩ :=
    parserSlotFactsAt frame 48 136 hframeRoom (by omega)
  obtain ⟨h520, h521, h522, h523⟩ :=
    parserSlotFactsAt frame 52 136 hframeRoom (by omega)
  obtain ⟨h880, h881, h882, h883⟩ :=
    parserSlotFactsAt frame 88 136 hframeRoom (by omega)
  obtain ⟨h920, h921, h922, h923⟩ :=
    parserSlotFactsAt frame 92 136 hframeRoom (by omega)
  obtain ⟨h960, h961, h962, h963⟩ :=
    parserSlotFactsAt frame 96 136 hframeRoom (by omega)
  obtain ⟨h1040, h1041, h1042, h1043⟩ :=
    parserSlotFactsAt frame 104 136 hframeRoom (by omega)
  obtain ⟨h1080, h1081, h1082, h1083⟩ :=
    parserSlotFactsAt frame 108 136 hframeRoom (by omega)
  have h1030 := (parserSlotFactsAt frame 103 136 hframeRoom (by omega)).1
  have hwideRoom : (frame + 32).toNat + 16 ≤ UInt32.size := by
    rw [show (frame + (32 : UInt32)).toNat = frame.toNat + 32 by
      simpa using h320]
    omega
  have hresultRoom24 : (frame + 24).toNat + 8 ≤ UInt32.size := by
    rw [show (frame + (24 : UInt32)).toNat = frame.toNat + 24 by
      simpa using h240]
    omega
  have hres28eq : (frame + 24) + 4 = frame + 28 := by
    rw [UInt32.add_assoc]
    rw [show (24 : UInt32) + 4 = 28 by decide]
  have h40eq : (frame + 32) + 8 = frame + 40 := by
    rw [UInt32.add_assoc]
    rw [show (32 : UInt32) + 8 = 40 by decide]
  have hmulBound := hinvariant.mulAcc_bound
  have hbyteFacts := canonicalDigitByteFacts hinvariant
  have hmask := canonicalDigitByte_mask hinvariant
  have hnextInvariant := hinvariant.takeCanonicalDigit
  have hnoOverflow := canonicalDigit_no_add_overflow hinvariant
  have hnextMachine : acc * 10 + UInt64.ofNat (digitNat c) =
      machineNextAccumulator acc c := rfl
  iintro ⟨Hruntime, Hglobal, Hbyte, HwideLow, HwideHigh,
    Hinner4, Hinner8, Hinner12, Hr24, Hr28,
    H64, H72, H80, H88, H92, H96, H103, H104, H108,
    H112, H120, H128, Hptr, Hlen, Hcont⟩
  simp only [decimalCheckedCallSegment, decimalCheckedTail,
    List.cons_append, List.nil_append]
  ihave HwideLow' : pointsTo_u64 ((frame + 32) + 0) oldWideLow $$
      [HwideLow]
  · rw [UInt32.add_zero]
    iexact HwideLow
  ihave HwideHigh' : pointsTo_u64 ((frame + 32) + 8) oldWideHigh $$
      [HwideHigh]
  · rw [h40eq]
    iexact HwideHigh
  have Hwide := wideMul_call_twp (α := α)
    (frame + 32) acc oldWideLow oldWideHigh hmulBound hwideRoom
    (callerLocals :=
      ⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
        decimalCheckedLocals frame l5 l6 l7 l12 currentPtr
          currentPtr currentLength (1 + currentPtr)
          (currentLength - 1) 10 acc 0
          l21 l22 l23 l24 l25 l26 l27 l28 l29, []⟩)
    (stack := [])
    (code := decimalCheckedTail) (arity := arity)
    (remainder := remainder) (controls := controls) (calls := calls)
    (s := s) (E := E) (Φ := Φ)
  simp only [decimalCheckedTail, List.cons_append, List.nil_append,
    List.append_nil] at Hwide
  iapply Hwide
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [HwideLow']
  · iexact HwideLow'
  isplitl [HwideHigh']
  · iexact HwideHigh'
  iintro Hruntime HwideLow HwideHigh
  ihave HwideLow' : pointsTo_u64 (frame + 32) (acc * 10) $$ [HwideLow]
  · rw [← UInt32.add_zero (frame + 32)]
    iexact HwideLow
  ihave HwideHigh' : pointsTo_u64 (frame + 40) 0 $$ [HwideHigh]
  · rw [← h40eq]
    iexact HwideHigh
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 0 h400 h401 h402 h403 h404
      h405 h406 h407 $$ HwideHigh'
  iintro HwideHigh
  iapply twp_neI64 (result := 0) (by decide)
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (acc * 10) h320 h321 h322 h323 h324
      h325 h326 h327 $$ HwideLow'
  iintro HwideLow
  iapply twp_localSet rfl
  simp only []
  iapply twp_block
  simp only [decimalCheckedBlockBody]
  iapply twp_block
  iapply twp_block
  iapply twp_block
  iapply twp_block
  simp only [decimalCheckedDecodeBody]
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_store64 old72 h720 h721 h722 h723 h724
      h725 h726 h727 $$ H72
  iintro H72
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply Wasm.SmallStep.twp_store64 old64 h640 h641 h642 h643 h644
      h645 h646 h647 $$ H64
  iintro H64
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hbyte' :
      (currentPtr + 0 ↦w (UInt8.ofNat c.toNat)) $$ [Hbyte]
  · rw [UInt32.add_zero]
    iexact Hbyte
  iapply twp_load8U (UInt8.ofNat c.toNat) (by simp) $$ Hbyte'
  iintro Hbyte
  rw [show (UInt8.ofNat c.toNat).toUInt32 = asciiByte32 c by rfl]
  iapply twp_store8_owned oldByte103 h1030 $$ H103
  iintro H103
  isimp [asciiByte32_toUInt8] at H103
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load8U (UInt8.ofNat c.toNat) h1030 $$ H103
  iintro H103
  rw [show (UInt8.ofNat c.toNat).toUInt32 = asciiByte32 c by rfl]
  iapply twp_const
  iapply twp_and
  rw [hmask]
  iapply twp_store32 old96 h960 h961 h962 h963 $$ H96
  iintro H96
  iapply twp_localGet rfl
  iapply twp_load32 (asciiByte32 c) h960 h961 h962 h963 $$ H96
  iintro H96
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  rw [UInt32.add_comm 24 frame]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  ihave Hr28' : pointsTo_u32 ((frame + 24) + 4) oldResult28 $$ [Hr28]
  · rw [hres28eq]
    iexact Hr28
  have Hparse := parseByte_call_twp (α := α)
    (frame + 24) (asciiByte32 c) 10 frame
    oldInner4 oldInner8 oldInner12 oldResult24 oldResult28
    (by decide) (by decide) hbyteFacts.1 hbyteFacts.2.1
    hinnerRoom hresultRoom24
    (callerLocals :=
      ⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
        decimalCheckedLocals frame l5 l6 l7 l12 currentPtr
          currentPtr currentLength (1 + currentPtr)
          (currentLength - 1) 10 acc 0 0 (acc * 10)
          (asciiByte32 c) l24 l25 l26 l27 l28 l29, []⟩)
    (stack := [])
    (code := decimalCheckedDecodeBody.drop 29)
    (arity := arity) (remainder := remainder)
    (controls :=
      { kind := .block
        paramArity := 0
        resultArity := 0
        body := decimalCheckedDecodeBody
        continuation := decimalCheckedOverflowBody
        belowStack := [] } ::
      { kind := .block
        paramArity := 0
        resultArity := 0
        body := .block 0 0 decimalCheckedDecodeBody ::
          decimalCheckedOverflowBody
        continuation := decimalCheckedAddBody
        belowStack := [] } ::
      { kind := .block
        paramArity := 0
        resultArity := 0
        body := .block 0 0
            (.block 0 0 decimalCheckedDecodeBody ::
              decimalCheckedOverflowBody) ::
          decimalCheckedAddBody
        continuation := decimalCheckedFailBody
        belowStack := [] } ::
      { kind := .block
        paramArity := 0
        resultArity := 0
        body := .block 0 0
            (.block 0 0
                (.block 0 0 decimalCheckedDecodeBody ::
                  decimalCheckedOverflowBody) ::
              decimalCheckedAddBody) ::
          decimalCheckedFailBody
        continuation := decimalCheckedCommitBody
        belowStack := [] } ::
      { kind := .block
        paramArity := 0
        resultArity := 0
        body := decimalCheckedBlockBody
        continuation := code
        belowStack := [] } :: controls)
    (calls := calls) (s := s) (E := E) (Φ := Φ)
  simp only [decimalCheckedDecodeBody, List.drop, List.append_nil,
    List.cons_append, List.nil_append] at Hparse
  iapply Hparse
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hinner4]
  · iexact Hinner4
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hr24]
  · iexact Hr24
  isplitl [Hr28']
  · iexact Hr28'
  iintro Hpost
  icases Hpost with ⟨Hruntime, Hglobal, Hinner4, Hinner8, Hinner12,
    Hr24, Hr28'⟩
  ihave Hr28 : pointsTo_u32 (frame + 28) (asciiByte32 c - 48) $$
      [Hr28']
  · rw [← hres28eq]
    iexact Hr28'
  iapply twp_localGet rfl
  iapply twp_load32 (asciiByte32 c - 48) h280 h281 h282 h283 $$ Hr28
  iintro Hr28
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 1 h240 h241 h242 h243 $$ Hr24
  iintro Hr24
  iapply twp_store32 old88 h880 h881 h882 h883 $$ H88
  iintro H88
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 old92 h920 h921 h922 h923 $$ H92
  iintro H92
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 1 h880 h881 h882 h883 $$ H88
  iintro H88
  iapply twp_store32 old104 h1040 h1041 h1042 h1043 $$ H104
  iintro H104
  iapply twp_localGet rfl
  iapply twp_load32 1 h1040 h1041 h1042 h1043 $$ H104
  iintro H104
  iapply twp_const
  iapply twp_and
  rw [show (1 : UInt32) &&& 1 = 1 by decide]
  iapply twp_brIf (by decide) rfl
  simp only [decimalCheckedAddBody, List.take_zero, List.drop_zero,
    List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (asciiByte32 c - 48) h920 h921 h922 h923 $$ H92
  iintro H92
  iapply twp_store32 old108 h1080 h1081 h1082 h1083 $$ H108
  iintro H108
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_load32 (asciiByte32 c - 48) h1080 h1081 h1082 h1083 $$ H108
  iintro H108
  iapply twp_extendUI32
  rw [hbyteFacts.2.2]
  iapply Wasm.SmallStep.twp_store64 old80 h800 h801 h802 h803 h804
      h805 h806 h807 $$ H80
  iintro H80
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (acc * 10) h720 h721 h722 h723 h724
      h725 h726 h727 $$ H72
  iintro H72
  iapply Wasm.SmallStep.twp_store64 acc h1120 h1121 h1122 h1123 h1124
      h1125 h1126 h1127 $$ H112
  iintro H112
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (acc * 10) h1120 h1121 h1122 h1123
      h1124 h1125 h1126 h1127 $$ H112
  iintro H112
  iapply twp_localSet rfl
  simp only []
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (UInt64.ofNat (digitNat c)) h800
      h801 h802 h803 h804 h805 h806 h807 $$ H80
  iintro H80
  iapply twp_addI64
  rw [hnextMachine]
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_ltUI64 (result := 0)
    ((if_neg hnoOverflow).symm)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_br rfl
  simp only [decimalCheckedCommitBody, List.take_zero, List.nil_append]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (acc * 10) h1120 h1121 h1122 h1123
      h1124 h1125 h1126 h1127 $$ H112
  iintro H112
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (UInt64.ofNat (digitNat c)) h800
      h801 h802 h803 h804 h805 h806 h807 $$ H80
  iintro H80
  iapply twp_addI64
  rw [hnextMachine]
  iapply Wasm.SmallStep.twp_store64 old128 h1280 h1281 h1282 h1283
      h1284 h1285 h1286 h1287 $$ H128
  iintro H128
  iapply twp_localGet rfl
  iapply twp_constI64
  iapply Wasm.SmallStep.twp_store64 old120 h1200 h1201 h1202 h1203
      h1204 h1205 h1206 h1207 $$ H120
  iintro H120
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply Wasm.SmallStep.twp_load64 (machineNextAccumulator acc c) h1280
      h1281 h1282 h1283 h1284 h1285 h1286 h1287 $$ H128
  iintro H128
  iapply Wasm.SmallStep.twp_store64 (acc * 10) h1120 h1121 h1122 h1123
      h1124 h1125 h1126 h1127 $$ H112
  iintro H112
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldPointer h480 h481 h482 h483 $$ Hptr
  iintro Hptr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldLength h520 h521 h522 h523 $$ Hlen
  iintro Hlen
  iapply Hcont
  isplit
  · ipureintro
    exact hnextInvariant
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hbyte]
  · iexact Hbyte
  isplitl [HwideLow]
  · iexact HwideLow
  isplitl [HwideHigh]
  · iexact HwideHigh
  isplitl [Hinner4]
  · iexact Hinner4
  isplitl [Hinner8]
  · iexact Hinner8
  isplitl [Hinner12]
  · iexact Hinner12
  isplitl [Hr24]
  · iexact Hr24
  isplitl [Hr28]
  · iexact Hr28
  isplitl [H64]
  · iexact H64
  isplitl [H72]
  · iexact H72
  isplitl [H80]
  · iexact H80
  isplitl [H88]
  · iexact H88
  isplitl [H92]
  · iexact H92
  isplitl [H96]
  · iexact H96
  isplitl [H103]
  · iexact H103
  isplitl [H104]
  · iexact H104
  isplitl [H108]
  · iexact H108
  isplitl [H112]
  · iexact H112
  isplitl [H120]
  · iexact H120
  isplitl [H128]
  · iexact H128
  isplitl [Hptr]
  · iexact Hptr
  iexact Hlen

/-- Empty-remaining branch of the exact generated checked-loop guard.  The
depth-five target belongs to `func51`'s surrounding nested blocks and is the
same success epilogue the simple loop exits into. -/
theorem decimalCheckedLoop_empty_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength frame : UInt32)
    (localValues : List Value)
    (hframeLocal :
      (⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          localValues, []⟩ : Locals).get 4 = some (.i32 frame))
    (hframeRoom : frame.toNat + 136 ≤ UInt32.size)
    {code targetCode : Program} {arity : Nat}
    {remainder targetValues : List Value}
    {controls targetControls : List ControlFrame}
    {calls : List CallFrame}
    (htarget : branchTarget? arity 5
      ({ kind := .loop
         paramArity := 0
         resultArity := 0
         body := decimalCheckedLoopBody
         continuation := code
         belowStack := [] } :: controls) [] =
      some (targetCode, targetControls, targetValues)) :
    pointsTo_u32 (frame + 52) 0 ∗
      (pointsTo_u32 (frame + 52) 0 -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              localValues, targetValues⟩,
            targetCode, arity, remainder, targetControls, calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          localValues, []⟩,
        decimalCheckedLoopBody, arity, remainder,
        { kind := .loop
          paramArity := 0
          resultArity := 0
          body := decimalCheckedLoopBody
          continuation := code
          belowStack := [] } :: controls,
        calls⟩ : Expr α) @ s; E [{ Φ }] := by
  obtain ⟨h520, h521, h522, h523⟩ :=
    parserSlotFactsAt frame 52 136 hframeRoom (by omega)
  iintro ⟨Hlength, Hfinish⟩
  simp only [decimalCheckedLoopBody, List.cons_append, List.nil_append]
  iapply twp_localGet hframeLocal
  iapply twp_load32 0 h520 h521 h522 h523 $$ Hlength
  iintro Hlength
  iapply twp_const
  iapply twp_geU (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  have Hbranch := twp_brIf (α := α) (s := s) (E := E) (Φ := Φ)
    (params := fromAsciiRadixParams resultPtr textPtr textLength 10)
    (localValues := localValues) (values := []) (condition := 1)
    (depth := 5) (arity := arity) (code := decimalCheckedLoopAfterGuard)
    (targetCode := targetCode) (remainder := remainder)
    (controls :=
      { kind := .loop, paramArity := 0, resultArity := 0
        body := decimalCheckedLoopBody, continuation := code
        belowStack := [] } :: controls)
    (targetControl := targetControls) (targetValues := targetValues)
    (calls := calls) (by decide) htarget
  simp only [decimalCheckedLoopAfterGuard, decimalCheckedPrepareSegment,
    decimalCheckedCallSegment, decimalCheckedTail,
    List.cons_append, List.nil_append] at Hbranch
  iapply Hbranch
  iapply Hfinish $$ Hlength

/-- Total well-founded wrapper for the exact generated checked decimal loop.
The nonempty premise is designed to be discharged by
`decimalCheckedLoop_backedge_twp`; the empty premise is discharged by
`decimalCheckedLoop_empty_twp`. -/
theorem decimalCheckedLoop_wf
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (locals : List Char → Locals)
    (I : List Char → IProp WasmHeapGF)
    (initial : List Char)
    {code : Program} {arity : Nat} {remainder belowStack : List Value}
    {controls : List ControlFrame} {calls : List CallFrame}
    (hbelow : belowStack = (locals initial).values.drop 0)
    (empty_closes :
      ⊢@{IProp WasmHeapGF} (iprop%
        I [] -∗
          WP (loopBodyExpr (α := α) (locals []) 0 0 arity
            decimalCheckedLoopBody code remainder belowStack controls calls)
          @ s; E [{ Φ }]))
    (nonempty_closes : ∀ c rest,
      ⊢@{IProp WasmHeapGF} (iprop%
        (I rest -∗
          WP (loopBodyExpr (α := α) (locals rest) 0 0 arity
            decimalCheckedLoopBody code remainder belowStack controls calls)
          @ s; E [{ Φ }]) -∗
        I (c :: rest) -∗
          WP (loopBodyExpr (α := α) (locals (c :: rest)) 0 0 arity
            decimalCheckedLoopBody code remainder belowStack controls calls)
          @ s; E [{ Φ }])) :
    I initial ⊢
      WP (.running
        ⟨locals initial,
          .loop 0 0 decimalCheckedLoopBody :: code,
          arity, remainder, controls, calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iapply Wasm.SmallStep.twp_loop_wf_family
    (measure := fun remaining : List Char => remaining.length)
    (locals := locals) (I := I) (initial := initial)
    (initialLocals := locals initial)
    (paramArity := 0) (resultArity := 0)
    (body := decimalCheckedLoopBody) (code := code)
    (belowStack := belowStack) rfl hbelow
  · intro remaining
    cases remaining with
    | nil =>
        iintro _ Hinv
        iapply empty_closes
        iexact Hinv
    | cons c rest =>
        iintro Hrec Hinv
        ispecialize Hrec $$ %rest
        ihave Hnext :
            (I rest -∗
              WP (loopBodyExpr (α := α) (locals rest) 0 0 arity
                decimalCheckedLoopBody code remainder belowStack
                controls calls) @ s; E [{ Φ }]) $$ [Hrec]
        · iintro Hrest
          iapply Hrec
          · ipureintro
            simp
          · iexact Hrest
        iapply nonempty_closes c rest $$ Hnext Hinv

/-- Exact total prologue rule for generated `func51`.  It owns precisely the
two frame words overwritten by the prologue and exposes the radix-validation
block as the continuation point. -/
theorem fromAsciiRadix_init_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength radix stackTop : UInt32)
    (oldPtr oldLength : UInt32)
    (hframeRoom : (stackTop - 144).toNat + 56 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 144) + 48) oldPtr ∗
      pointsTo_u32 ((stackTop - 144) + 52) oldLength ∗
      (globalPointsTo 0 (.i32 (stackTop - 144)) -∗
        pointsTo_u32 ((stackTop - 144) + 48) textPtr -∗
        pointsTo_u32 ((stackTop - 144) + 52) textLength -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength radix,
              fromAsciiRadixFramedLocals (stackTop - 144), []⟩,
            fromAsciiRadixAfterInit, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength radix,
          fromAsciiRadixZeroLocals, []⟩,
        func51, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let frame := stackTop - 144
  obtain ⟨hp0, hp1, hp2, hp3⟩ :=
    parserSlotFacts frame 48 hframeRoom (by decide)
  obtain ⟨hl0, hl1, hl2, hl3⟩ :=
    parserSlotFacts frame 52 hframeRoom (by decide)
  iintro ⟨Hglobal, Hptr, Hlength, Hcont⟩
  simp only [func51]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [fromAsciiRadixParams, fromAsciiRadixZeroLocals,
    fromAsciiRadixFramedLocals, func51Def, List.map_cons,
    List.map_nil, ValueType.zero, List.length_cons, List.length_nil,
    Nat.reduceAdd, Nat.reduceSub, List.set]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldPtr hp0 hp1 hp2 hp3 $$ Hptr
  iintro Hptr
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_store32 oldLength hl0 hl1 hl2 hl3 $$ Hlength
  iintro Hlength
  simp only [fromAsciiRadixAfterInit, func51, List.drop]
  iapply Hcont $$ Hglobal Hptr Hlength

/-- Exact successful radix-validation rule.  The unchanged wrapper always
passes radix ten, so both generated failure branches are unreachable. -/
theorem fromAsciiRadix_radixTen_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength : UInt32)
    (localValues : List Value)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          localValues, []⟩,
        fromAsciiRadixAfterRadixCheck, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          localValues, []⟩,
        fromAsciiRadixAfterInit, 0, [], [], calls⟩ : Expr α)
      @ s; E [{ Φ }] := by
  iintro Hcont
  simp only [fromAsciiRadixAfterInit, fromAsciiRadixAfterRadixCheck,
    func51, List.drop]
  iapply twp_block
  iapply twp_block
  iapply twp_const
  iapply twp_localGet rfl
  iapply twp_gtU (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_brIfZero
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_gtU (result := 0) (by decide)
  iapply twp_const
  iapply twp_and
  rw [show (0 : UInt32) &&& 1 = 0 by decide]
  iapply twp_eqz (result := 1) (by decide)
  iapply twp_brIf (by decide) rfl
  simp only [List.take_zero, List.drop_zero, List.nil_append]
  iexact Hcont

/-- Composed exact prefix for the call produced by `u64::from_str`: install
the generated frame, record the input slice, and discharge radix validation
for ten. -/
theorem fromAsciiRadix_decimal_prefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength stackTop : UInt32)
    (oldPtr oldLength : UInt32)
    (hframeRoom : (stackTop - 144).toNat + 56 ≤ UInt32.size)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 144) + 48) oldPtr ∗
      pointsTo_u32 ((stackTop - 144) + 52) oldLength ∗
      (globalPointsTo 0 (.i32 (stackTop - 144)) -∗
        pointsTo_u32 ((stackTop - 144) + 48) textPtr -∗
        pointsTo_u32 ((stackTop - 144) + 52) textLength -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              fromAsciiRadixFramedLocals (stackTop - 144), []⟩,
            fromAsciiRadixAfterRadixCheck, 0, [], [], calls⟩ : Expr α)
          @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
          fromAsciiRadixZeroLocals, []⟩,
        func51, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hptr, Hlength, Hcont⟩
  iapply fromAsciiRadix_init_twp
    resultPtr textPtr textLength 10 stackTop oldPtr oldLength hframeRoom
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hptr]
  · iexact Hptr
  isplitl [Hlength]
  · iexact Hlength
  iintro Hglobal Hptr Hlength
  iapply fromAsciiRadix_radixTen_twp
  iapply Hcont $$ Hglobal Hptr Hlength

private def u64FromStrParams
    (resultPtr textPtr textLength : UInt32) : List Value :=
  [.i32 resultPtr, .i32 textPtr, .i32 textLength]

private def stringParseParams
    (resultPtr textPtr textLength : UInt32) : List Value :=
  [.i32 resultPtr, .i32 textPtr, .i32 textLength]

private def parseClosureParams
    (closurePtr textPtr textLength : UInt32) : List Value :=
  [.i32 closurePtr, .i32 textPtr, .i32 textLength]

private def parseClosureZeroLocals : List Value := [.i32 0, .i64 0]

private def parseClosureLocals (frame : UInt32) (value : UInt64) : List Value :=
  [.i32 frame, .i64 value]

/-- Remaining closure body immediately after the `str::parse` call. -/
def parseClosureAfterParse : Program := func2.drop 12

/-- Exact total forwarding rule for local `func53` (`u64::from_str`).

The premise is the clearly exposed `func51` call boundary: arguments are
`(resultPtr, textPtr, textLength, 10)` and the next instruction is this
wrapper's generated `ret`.
-/
theorem u64FromStr_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨u64FromStrParams resultPtr textPtr textLength, [],
          [.i32 10, .i32 textLength, .i32 textPtr, .i32 resultPtr]⟩,
        [.call 53, .ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨u64FromStrParams resultPtr textPtr textLength, [], []⟩,
        func53, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  simp only [func53]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_const
  iexact Hcont

/-- `func53` composed through its absolute-index-`53` call into the verified
decimal prefix of generated `func51`.  The continuation is inside `func51`,
ready for the sign/empty checks and the digit loops. -/
theorem u64FromStr_to_decimalPrefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength stackTop : UInt32)
    (oldPtr oldLength : UInt32)
    (hframeRoom : (stackTop - 144).toNat + 56 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 144) + 48) oldPtr ∗
      pointsTo_u32 ((stackTop - 144) + 52) oldLength ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 144)) -∗
        pointsTo_u32 ((stackTop - 144) + 48) textPtr -∗
        pointsTo_u32 ((stackTop - 144) + 52) textLength -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              fromAsciiRadixFramedLocals (stackTop - 144), []⟩,
            fromAsciiRadixAfterRadixCheck, 0, [], [],
            { locals :=
                ⟨u64FromStrParams resultPtr textPtr textLength, [], []⟩
              continuation := [.ret]
              resultArity := 0
              callerRemainder := []
              control := [] } :: calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨u64FromStrParams resultPtr textPtr textLength, [], []⟩,
        func53, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hruntime, Hglobal, Hptr, Hlength, Hcont⟩
  iapply u64FromStr_body_twp
  iapply Wasm.SmallStep.twp_call (α := α) «module» 53 func51Def
      (by decide) u64FromAsciiRadix_index $$ Hruntime
  iintro Hruntime
  have Hprefix := fromAsciiRadix_decimal_prefix_twp (α := α)
    resultPtr textPtr textLength stackTop oldPtr oldLength hframeRoom
    (s := s) (E := E) (Φ := Φ)
    (calls :=
      { locals := ⟨u64FromStrParams resultPtr textPtr textLength, [], []⟩
        continuation := [.ret]
        resultArity := 0
        callerRemainder := []
        control := [] } :: calls)
  simp only [fromAsciiRadixParams, fromAsciiRadixZeroLocals, func51Def,
    List.map_cons, List.map_nil, ValueType.zero] at Hprefix
  simp [func51Def, fromAsciiRadixParams, Function.toLocals,
    Function.numParams, ValueType.zero]
  iapply Hprefix
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hptr]
  · iexact Hptr
  isplitl [Hlength]
  · iexact Hlength
  iintro Hglobal Hptr Hlength
  iapply Hcont $$ Hruntime Hglobal Hptr Hlength

/-- Exact total forwarding rule for local `func81` (`str::parse`). -/
theorem stringParse_body_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength : UInt32)
    {calls : List CallFrame} :
    WP (.running
      ⟨⟨stringParseParams resultPtr textPtr textLength, [],
          [.i32 textLength, .i32 textPtr, .i32 resultPtr]⟩,
        [.call 55, .ret], 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] ⊢
    WP (.running
      ⟨⟨stringParseParams resultPtr textPtr textLength, [], []⟩,
        func81, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro Hcont
  simp only [func81]
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  iexact Hcont

/-- `func81` composed through `func53` into the verified `func51` decimal
prefix.  This discharges both thin standard-library wrappers used by the
driver's parse closure. -/
theorem stringParse_to_decimalPrefix_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (resultPtr textPtr textLength stackTop : UInt32)
    (oldPtr oldLength : UInt32)
    (hframeRoom : (stackTop - 144).toNat + 56 ≤ UInt32.size)
    {calls : List CallFrame} :
    runtimeModuleOwn «module» ∗
      globalPointsTo 0 (.i32 stackTop) ∗
      pointsTo_u32 ((stackTop - 144) + 48) oldPtr ∗
      pointsTo_u32 ((stackTop - 144) + 52) oldLength ∗
      (runtimeModuleOwn «module» -∗
        globalPointsTo 0 (.i32 (stackTop - 144)) -∗
        pointsTo_u32 ((stackTop - 144) + 48) textPtr -∗
        pointsTo_u32 ((stackTop - 144) + 52) textLength -∗
        WP (.running
          ⟨⟨fromAsciiRadixParams resultPtr textPtr textLength 10,
              fromAsciiRadixFramedLocals (stackTop - 144), []⟩,
            fromAsciiRadixAfterRadixCheck, 0, [], [],
            { locals :=
                ⟨u64FromStrParams resultPtr textPtr textLength, [], []⟩
              continuation := [.ret]
              resultArity := 0
              callerRemainder := []
              control := [] } ::
            { locals :=
                ⟨stringParseParams resultPtr textPtr textLength, [], []⟩
              continuation := [.ret]
              resultArity := 0
              callerRemainder := []
              control := [] } :: calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨stringParseParams resultPtr textPtr textLength, [], []⟩,
        func81, 0, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  let stringParseFrame : CallFrame :=
    { locals := ⟨stringParseParams resultPtr textPtr textLength, [], []⟩
      continuation := [.ret]
      resultArity := 0
      callerRemainder := []
      control := [] }
  iintro ⟨Hruntime, Hglobal, Hptr, Hlength, Hcont⟩
  iapply stringParse_body_twp
  iapply Wasm.SmallStep.twp_call (α := α) «module» 55 func53Def
      (by decide) u64FromStr_index $$ Hruntime
  iintro Hruntime
  have Hinner := u64FromStr_to_decimalPrefix_twp (α := α)
    resultPtr textPtr textLength stackTop oldPtr oldLength hframeRoom
    (s := s) (E := E) (Φ := Φ) (calls := stringParseFrame :: calls)
  simp only [u64FromStrParams] at Hinner
  simp [func53Def, u64FromStrParams, Function.toLocals,
    Function.numParams]
  iapply Hinner
  isplitl [Hruntime]
  · iexact Hruntime
  isplitl [Hglobal]
  · iexact Hglobal
  isplitl [Hptr]
  · iexact Hptr
  isplitl [Hlength]
  · iexact Hlength
  iintro Hruntime Hglobal Hptr Hlength
  dsimp only [stringParseFrame]
  iapply Hcont $$ Hruntime Hglobal Hptr Hlength

/-- Exact prefix rule for generated parse closure `func2`.  It installs the
thirty-two-byte shadow frame and exposes the absolute-index-`83` call to
`func81`, with its result area at `frame + 8`.
-/
theorem parseClosure_to_stringParse_twp
    [WasmSmallStepGS hlc]
    {s : Stuckness} {E : CoPset}
    {Φ : List Value → IProp WasmHeapGF}
    (closurePtr textPtr textLength stackTop : UInt32)
    {calls : List CallFrame} :
    globalPointsTo 0 (.i32 stackTop) ∗
      (globalPointsTo 0 (.i32 (stackTop - 32)) -∗
        WP (.running
          ⟨⟨parseClosureParams closurePtr textPtr textLength,
              parseClosureLocals (stackTop - 32) 0,
              [.i32 textLength, .i32 textPtr,
                .i32 (8 + (stackTop - 32))]⟩,
            .call 83 :: parseClosureAfterParse,
            1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }]) ⊢
    WP (.running
      ⟨⟨parseClosureParams closurePtr textPtr textLength,
          parseClosureZeroLocals, []⟩,
        func2, 1, [], [], calls⟩ : Expr α) @ s; E [{ Φ }] := by
  iintro ⟨Hglobal, Hcont⟩
  simp only [func2]
  iapply twp_globalGet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_const
  iapply twp_sub
  iapply twp_localSet rfl
  simp only [parseClosureParams, parseClosureZeroLocals]
  iapply twp_localGet rfl
  iapply twp_globalSet0
  isplitl [Hglobal]
  · iexact Hglobal
  iintro Hglobal
  iapply twp_localGet rfl
  iapply twp_const
  iapply twp_add
  iapply twp_localGet rfl
  iapply twp_localGet rfl
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd,
    Nat.reduceSub, List.set]
  simp only [parseClosureAfterParse, parseClosureLocals, func2, List.drop]
  iapply Hcont
  iexact Hglobal

end Project.Mergesort.ParseProof
