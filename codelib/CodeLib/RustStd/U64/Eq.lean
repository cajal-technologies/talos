import CodeLib.RustStd.U64.Basic

/-! `u64::eq` (`a == b`) — inlined to `i64.eq; i32.const 1; i32.and` (an `i64.eq`
whose `0/1` result is `bool`-normalised by a redundant `& 1`). Chunk fact + export
body, reusing the trunk's `CmpChunk`/`cmpBodyWp`. This file is the **exemplar** for
the comparison (`cmp`) shape — `ne`/`lt`/`le`/`gt`/`ge` mirror it with their own
opcode. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The inlined comparison chunk `[.eqI64, .const 1, .and]` computes the `i32`
boolean `if a = b then 1 else 0` on stack operands (the `& 1` mask is a no-op on
the already-`0/1` `i64.eq` result, discharged here). Reusable wherever `a == b`
is inlined. -/
theorem eq_chunk : CmpChunk (T := UInt64) [.eqI64, .const 1, .and] (fun a b => if a = b then 1 else 0) := by
  intro α m env Q st P L rest a b vs
  have hmask : (1 : UInt32) &&& (if a = b then 1 else 0) = (if a = b then 1 else 0) := by
    split <;> decide
  simp only [List.cons_append, List.nil_append, toV_u64, wp_eqI64_cons, wp_const_cons,
    wp_and_cons, hmask]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::eq`, built by reusing `eq_chunk`. -/
theorem eqBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) :
    wp m ([.localGet 0, .localGet 1] ++ [.eqI64, .const 1, .and] ++ [.ret])
      (Returns (.i32 (if a = b then 1 else 0) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env :=
  cmpBodyWp eq_chunk st a b vs

/-- Concrete-`i64` restatement of `eq_chunk` (matches the emitted opcodes for `rw`
at an inlined `a == b`), proven *by reusing* the polymorphic `eq_chunk`. -/
theorem eq_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value) :
    wp m (.eqI64 :: .const 1 :: .and :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 (if a = b then 1 else 0) :: vs⟩ env :=
  eq_chunk a b vs

end Wasm.RustStd.U64
