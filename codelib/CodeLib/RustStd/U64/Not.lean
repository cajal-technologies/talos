import CodeLib.RustStd.U64.Basic

/-! `u64::not` (`!a`) — inlined to `constI64 0xFFFF…FFFF; xor`. The
`a ^^^ MAX_U64 = ~~~a` identity is the only `bv_decide` here, proven once in the
chunk and reused by the concrete restatement. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

abbrev MAX_U64 : UInt64 := 0xFFFF_FFFF_FFFF_FFFF

/-- The reusable chunk: `[.constI64 MAX_U64, .xorI64]` computes `~~~` on a stack
operand. The `a ^^^ MAX_U64 = ~~~a` `bv_decide` lives here, once. -/
theorem not_chunk : UnChunk (T := UInt64) [.constI64 MAX_U64, .xorI64] (~~~ ·) := by
  intro α hlc inst s E Φ params localValues rest arity remainder
    controls calls a vs
  simp only [toV_u64, List.cons_append, List.nil_append]
  iintro Hwp
  iapply Wasm.SmallStep.wp_constI64
  inext
  have hnot : a ^^^ MAX_U64 = ~~~a := by
    simp [MAX_U64]
    bv_decide
  iapply Wasm.SmallStep.wp_xorI64
  simp only [hnot]
  inext
  iexact Hwp

end Wasm.RustStd.U64
