import CodeLib.RustStd.U64.Basic

/-! `u64::add` — inlined to a single `i64.addI64`. Chunk fact + concrete
restatement, reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The reusable chunk: `[.addI64]` computes `+` on stack operands. Feeds the
export-body spec via `binBodyReturnsWp`; also `rw`-able at an inlined `i64.add`. -/
theorem add_chunk : BinChunk [.addI64] ((· + ·) : UInt64 → UInt64 → UInt64) := by
  intro α m env Q st P L rest a b vs _
  simp only [List.cons_append, List.nil_append, toV_u64, wp_addI64_cons]

/-- Concrete `i64` restatement of `add_chunk` for `rw`/`simp` at an inlined `i64.add`. -/
theorem add_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.addI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a + b) :: vs⟩ env := by
  simpa only [toV_u64, List.cons_append, List.nil_append]
    using add_chunk (rest := rest) a b vs trivial

end Wasm.RustStd.U64
