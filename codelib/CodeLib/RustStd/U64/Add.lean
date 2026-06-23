import CodeLib.RustStd.U64.Basic

/-! `u64::add` — inlined to local reads plus a single `i64.addI64`. Chunk fact + body, reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined chunk `[.addI64]` computes `+` after operands are read from locals. -/
theorem add_chunk : BinChunk (T := UInt64) [.addI64] (· + ·) := by
  intro α m env Q st P L rest i j a b vs ha hb
  simp only [toV_u64] at ha hb
  have hb' : (⟨P, L, .i64 a :: vs⟩ : Locals).get j = some (.i64 b) := by
    simpa [Locals.get] using hb
  simp only [List.cons_append, List.nil_append, toV_u64, wp_localGet_cons, ha, hb',
    wp_addI64_cons]

set_option maxRecDepth 4096 in
/-- Fallthrough body theorem for `rust_u64::add`, built by reusing `add_chunk`. -/
theorem addBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ [.addI64])
      (fun c => ∃ st',
        c = .Fallthrough st' ⟨[.i64 a, .i64 b], [], .i64 (a + b) :: vs⟩ ∧ framePost st st')
      st ⟨[.i64 a, .i64 b], [], vs⟩ env :=
  binBodyWp add_chunk st 0 1 a b vs rfl rfl

/-- Concrete `i64` restatement of `add_chunk` (matches emitted opcodes for `rw`
at an inlined `i64.add`), proven *by reusing* the polymorphic `add_chunk`. -/
theorem add_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.addI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a + b) :: vs⟩ env :=
  by simp only [wp_addI64_cons]

end Wasm.RustStd.U64
