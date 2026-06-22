import CodeLib.RustStd.U64.Basic

/-! `u64::ge` (`a >= b`) — inlined to `i64.ge_u; i32.const 1; i32.and`. Reuses the
trunk's `CmpChunk`/`cmpBodyWp` (the `cmp` shape, exemplar `U64/Eq.lean`). -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined chunk `[.geUI64, .const 1, .and]` computes the `i32` boolean
`if a ≥ b then 1 else 0` on stack operands (the `& 1` mask discharged here). -/
theorem ge_chunk : CmpChunk (T := UInt64) [.geUI64, .const 1, .and] (fun a b => if a ≥ b then 1 else 0) := by
  intro α m env Q st P L rest a b vs
  have hmask : (1 : UInt32) &&& (if a ≥ b then 1 else 0) = (if a ≥ b then 1 else 0) := by
    split <;> decide
  simp only [List.cons_append, List.nil_append, toV_u64, wp_geUI64_cons, wp_const_cons,
    wp_and_cons, hmask]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::ge`, built by reusing `ge_chunk`. -/
theorem geBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ [.geUI64, .const 1, .and] ++ [.ret])
      (Returns (.i32 (if a ≥ b then 1 else 0) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env :=
  cmpBodyWp ge_chunk st a b vs

/-- Concrete-`i64` restatement of `ge_chunk` (matches emitted opcodes for `rw` at
an inlined `a >= b`), proven *by reusing* the polymorphic `ge_chunk`. -/
theorem ge_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.geUI64 :: .const 1 :: .and :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 (if a ≥ b then 1 else 0) :: vs⟩ env :=
  ge_chunk a b vs

end Wasm.RustStd.U64
