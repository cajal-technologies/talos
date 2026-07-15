import CodeLib.RustStd.U64.Basic

/-! `u64::bitor` — inlined to a single `i64.orI64`. Chunk fact + concrete
restatement, reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The reusable chunk: `[.orI64]` computes `|||` on stack operands. -/
theorem bitor_chunk : BinChunk [.orI64] ((· ||| ·) : UInt64 → UInt64 → UInt64) := by
  intro α m env Q st P L rest a b vs _
  simp only [List.cons_append, List.nil_append, toV_u64, wp_orI64_cons]

/-- Concrete `i64` restatement for `rw`/`simp` at an inlined `i64.or`. -/
theorem bitor_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.orI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a ||| b) :: vs⟩ env := by
  simpa only [toV_u64, List.cons_append, List.nil_append]
    using bitor_chunk (rest := rest) a b vs trivial

end Wasm.RustStd.U64
