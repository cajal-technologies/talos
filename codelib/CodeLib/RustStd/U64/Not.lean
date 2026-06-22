import CodeLib.RustStd.U64.Basic

/-! `u64::not` (`!a`) — inlined to `constI64 0xFFFF…FFFF; xor`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined chunk `[.constI64 allOnes, .xorI64]` computes `~~~a`. -/
theorem not_chunk : UnChunk (T := UInt64) [.constI64 18446744073709551615, .xorI64] (~~~ ·) := by
  intro α m env Q st P L rest a vs
  simp only [List.cons_append, List.nil_append, toV_u64, wp_constI64_cons, wp_xorI64_cons]
  rw [show a ^^^ 18446744073709551615 = ~~~a from by bv_decide]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::not`, reusing `not_chunk`. -/
theorem notBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (vs : List Value) :
    wp m ([.localGet 0] ++ [.constI64 18446744073709551615, .xorI64] ++ [.ret])
      (Returns (.i64 (~~~a) :: vs) (framePost st)) st ⟨[.i64 a], [], vs⟩ env :=
  unBodyWp not_chunk st a vs

/-- Concrete `i64` restatement of `not_chunk` for `rw`/`simp` at an inlined `not`. -/
theorem not_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (vs : List Value) :
    wp m (.constI64 18446744073709551615 :: .xorI64 :: rest) Q st ⟨P, L, .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (~~~a) :: vs⟩ env :=
  not_chunk a vs

end Wasm.RustStd.U64
