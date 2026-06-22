import CodeLib.RustStd.U64.Basic

/-! `u64::lt` (`a < b`) — inlined to `i64.lt_u; i32.const 1; i32.and`. Reuses the
trunk's `CmpChunk`/`cmpBodyWp` (the `cmp` shape, exemplar `U64/Eq.lean`). -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined chunk `[.ltUI64, .const 1, .and]` computes the `i32` boolean
`if a < b then 1 else 0` on stack operands (the `& 1` mask discharged here). -/
theorem lt_chunk : CmpChunk (T := UInt64) [.ltUI64, .const 1, .and] (fun a b => if a < b then 1 else 0) := by
  intro α m env Q st P L rest a b vs
  have hmask : (1 : UInt32) &&& (if a < b then 1 else 0) = (if a < b then 1 else 0) := by
    split <;> decide
  simp only [List.cons_append, List.nil_append, toV_u64, wp_ltUI64_cons, wp_const_cons,
    wp_and_cons, hmask]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::lt`, built by reusing `lt_chunk`. -/
theorem ltBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ [.ltUI64, .const 1, .and] ++ [.ret])
      (Returns (.i32 (if a < b then 1 else 0) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env :=
  cmpBodyWp lt_chunk st a b vs

/-- Concrete-`i64` restatement of `lt_chunk` (matches emitted opcodes for `rw` at
an inlined `a < b`), proven *by reusing* the polymorphic `lt_chunk`. -/
theorem lt_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.ltUI64 :: .const 1 :: .and :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 (if a < b then 1 else 0) :: vs⟩ env :=
  lt_chunk a b vs

end Wasm.RustStd.U64
