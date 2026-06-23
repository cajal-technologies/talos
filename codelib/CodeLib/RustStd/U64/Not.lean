import CodeLib.RustStd.U64.Basic

/-! `u64::not` (`!a`) — inlined to a local read, then `constI64 0xFFFF…FFFF; xor`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

def MAX_U64 : UInt64 := 0xFFFF_FFFF_FFFF_FFFF

/-- The inlined chunk `[.constI64 allOnes, .xorI64]` computes `~~~a` after reading a local. -/
theorem not_chunk : UnChunk (T := UInt64) [.constI64 MAX_U64, .xorI64] (~~~ ·) := by
  intro α m env Q st P L rest i a vs ha
  simp only [List.cons_append, List.nil_append, toV_u64, wp_localGet_cons, ha,
    wp_constI64_cons, wp_xorI64_cons]
  rw [show a ^^^ MAX_U64 = ~~~a from by
    simp [MAX_U64]
    bv_decide]

set_option maxRecDepth 4096 in
/-- Fallthrough body theorem for `rust_u64::not`, reusing `not_chunk`. -/
theorem notBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (vs : List Value) :
    wp m ([.localGet 0] ++ [.constI64 MAX_U64, .xorI64])
      (fun c => ∃ st',
        c = .Fallthrough st' ⟨[.i64 a], [], .i64 (~~~a) :: vs⟩ ∧ framePost st st')
      st ⟨[.i64 a], [], vs⟩ env :=
  unBodyWp not_chunk st 0 a vs rfl

/-- Concrete `i64` restatement of `not_chunk` for `rw`/`simp` at an inlined `not`. -/
theorem not_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (vs : List Value) :
    wp m (.constI64 MAX_U64 :: .xorI64 :: rest) Q st ⟨P, L, .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (~~~a) :: vs⟩ env :=
  by
    simp only [wp_constI64_cons, wp_xorI64_cons]
    rw [show a ^^^ MAX_U64 = ~~~a from by
      simp [MAX_U64]
      bv_decide]

end Wasm.RustStd.U64
