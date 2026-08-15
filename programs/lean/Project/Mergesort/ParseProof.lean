import Project.Mergesort.TextProof
import Project.Mergesort.RangeProof

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
open Project.Mergesort.TextProof

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
