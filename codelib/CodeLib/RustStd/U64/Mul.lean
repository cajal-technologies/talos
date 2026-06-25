import CodeLib.RustStd.U64.Basic

/-! `u64::mul` — inlined to a single `i64.mulI64`. Chunk fact + concrete
restatement, reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The reusable chunk: `[.mulI64]` computes `*` on stack operands. -/
theorem mul_chunk : BinChunk [.mulI64] ((· * ·) : UInt64 → UInt64 → UInt64) := by
  intro α m env Q st P L rest a b vs _
  simp only [List.cons_append, List.nil_append, toV_u64, wp_mulI64_cons]

/-- Concrete `i64` restatement for `rw`/`simp` at an inlined `i64.mul`. -/
theorem mul_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.mulI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a * b) :: vs⟩ env := by
  simpa only [toV_u64, List.cons_append, List.nil_append]
    using mul_chunk (rest := rest) a b vs trivial

end Wasm.RustStd.U64
