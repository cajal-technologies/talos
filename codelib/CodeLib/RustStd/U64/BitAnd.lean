import CodeLib.RustStd.U64.Basic

/-! `u64::bitand` — inlined to a single `i64.andI64`. Chunk fact + export body, reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined chunk `[.andI64]` computes `&&&` on stack operands (reusable wherever
`a &&& b` is inlined). -/
theorem bitand_chunk : BinChunk (T := UInt64) [.andI64] (· &&& ·) := by
  intro α m env Q st P L rest a b vs
  simp only [List.cons_append, List.nil_append, toV_u64, wp_andI64_cons]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::bitand`, built by reusing `bitand_chunk`. -/
theorem bitandBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ [.andI64] ++ [.ret])
      (Returns (.i64 (a &&& b) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env :=
  binBodyWp bitand_chunk st a b vs

/-- Concrete `i64` restatement (matches emitted opcodes for `rw`/`simp` at an
inlined `i64.and`), reusing the polymorphic chunk. -/
theorem and_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.andI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a &&& b) :: vs⟩ env :=
  bitand_chunk a b vs

end Wasm.RustStd.U64
