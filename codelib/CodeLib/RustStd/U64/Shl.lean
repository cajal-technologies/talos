import CodeLib.RustStd.U64.Basic

/-! `u64::shl` (`a << b`, `b : u32`) — inlined as the shared mask-extend-shift
prefix followed by `shlI64`, a shift by `b % 64`. The `b % 64` normalisation is
the trunk-level `shiftAmount_norm` (shared with `shr`), so there is no
`bv_decide` in this file. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The reusable chunk for `a << b` (heterogeneous: `a : u64`, `b : u32`): the
mask-extend-shift sequence on stack operands, normalising the count via
`shiftAmount_norm`. -/
theorem shl_chunk :
    BinChunk (A := UInt64) (B := UInt32) (C := UInt64)
      (shiftAmountFrag ++ [.shlI64]) (fun a b => a <<< (b.toUInt64 % 64)) := by
  intro α m env Q st P L rest a b vs _
  simp only [shiftAmountFrag, List.cons_append, List.nil_append, toV_u64, toV_u32,
    wp_const_cons, wp_and_cons, wp_extendUI32_cons, wp_shlI64_cons, shiftAmount_norm]

/-- Concrete restatement of `shl_chunk` for `rw`/`simp` at an inlined `a << b`. -/
theorem shl_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (b : UInt32)
    (vs : List Value) :
    wp m (.const shiftMask :: .and :: .extendUI32 :: .shlI64 :: rest) Q st
        ⟨P, L, .i32 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a <<< (b.toUInt64 % 64)) :: vs⟩ env := by
  simpa only [shiftAmountFrag, toV_u64, toV_u32, List.cons_append, List.nil_append]
    using shl_chunk (rest := rest) a b vs trivial

end Wasm.RustStd.U64
