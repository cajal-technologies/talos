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
open Project.Mergesort.RangeProof
open Project.Mergesort.TextProof

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
