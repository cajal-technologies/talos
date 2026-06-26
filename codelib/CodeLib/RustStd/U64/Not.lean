import CodeLib.RustStd.U64.Basic

/-! `u64::not` (`!a`) — inlined to `constI64 0xFFFF…FFFF; xor`. The
`a ^^^ MAX_U64 = ~~~a` identity is the only `bv_decide` here, proven once in the
chunk and reused by the concrete restatement. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

abbrev MAX_U64 : UInt64 := 0xFFFF_FFFF_FFFF_FFFF

/-- The reusable chunk: `[.constI64 MAX_U64, .xorI64]` computes `~~~` on a stack
operand. The `a ^^^ MAX_U64 = ~~~a` `bv_decide` lives here, once. -/
theorem not_chunk : UnChunk (T := UInt64) [.constI64 MAX_U64, .xorI64] (~~~ ·) := by
  intro α m env Q st P L rest a vs
  simp only [List.cons_append, List.nil_append, toV_u64, wp_constI64_cons, wp_xorI64_cons]
  rw [show a ^^^ MAX_U64 = ~~~a from by simp [MAX_U64]; bv_decide]

/-- Concrete `i64` restatement of `not_chunk` for `rw`/`simp` at an inlined `not`. -/
theorem not_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (vs : List Value) :
    wp m (.constI64 MAX_U64 :: .xorI64 :: rest) Q st ⟨P, L, .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (~~~a) :: vs⟩ env := by
  simpa only [toV_u64, List.cons_append, List.nil_append] using not_chunk (rest := rest) a vs

end Wasm.RustStd.U64
