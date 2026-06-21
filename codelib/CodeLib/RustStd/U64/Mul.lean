import CodeLib.RustStd.U64.Basic

/-! `u64::mul` — inlined to a single `i64.mulI64`. Chunk fact + export body, reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined chunk `[.mulI64]` computes `*` on stack operands (reusable wherever
`a * b` is inlined). -/
theorem mul_chunk : BinChunk (T := UInt64) [.mulI64] (· * ·) := by
  intro α m env Q st P L rest a b vs
  simp only [List.cons_append, List.nil_append, toV_u64, wp_mulI64_cons]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::mul`, built by reusing `mul_chunk`. -/
theorem mulBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ [.mulI64] ++ [.ret])
      (Returns (.i64 (a * b) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env :=
  binBodyWp mul_chunk st a b vs

/-- Concrete `i64` restatement (matches emitted opcodes for `rw`/`simp` at an
inlined `i64.mul`), reusing the polymorphic chunk. -/
theorem mul_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.mulI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a * b) :: vs⟩ env :=
  mul_chunk a b vs

end Wasm.RustStd.U64
