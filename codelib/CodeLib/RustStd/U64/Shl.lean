import CodeLib.RustStd.U64.Basic

/-! `u64::shl` (`a << b`, `b : u32`) — inlined as the mask-extend-shift sequence
`const 63; and; extendUI32; shlI64`, a shift by `b % 64`.

The reusable unit is `shl_seq`: a chunk theorem about that inlined sequence run
on stack operands. It is width-specific (the `extendUI32` and the mask `63`), so
it lives here rather than in the trunk, but it plays the same role as `add_seq`
— the *same* theorem discharges an inlined `a << b` (rewrite it at the
occurrence, with the `shlI64` atomic excluded) and the called export body
(`shlBodyWp`). -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- Chunk theorem: the inlined `const 63; and; extendUI32; shlI64` sequence, run
on `i32 b :: i64 a` operands, computes `a <<< (b % 64)`. Reuse this wherever
`a << b` is inlined; the `b % 64` normalisation is baked in once here. -/
theorem shl_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (b : UInt32)
    (vs : List Value) :
    wp m (.const 63 :: .and :: .extendUI32 :: .shlI64 :: rest) Q st
        ⟨P, L, .i32 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a <<< (b.toUInt64 % 64)) :: vs⟩ env := by
  have hamt : a <<< (UInt64.ofNat (63 &&& b).toNat % 64) = a <<< (b.toUInt64 % 64) := by
    simp; bv_decide
  simp only [wp_const_cons, wp_and_cons, wp_extendUI32_cons, wp_shlI64_cons, hamt]

/-- Verbatim opt-0 body of `rust_u64::shl`. -/
def shlBody : Program :=
  [ .localGet 0, .localGet 1, .const 63, .and, .extendUI32, .shlI64, .ret ]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::shl`, built by **reusing** `shl_seq`
(the `shlI64` atomic is never touched here — the chunk is the only path). -/
theorem shlBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt32) (vs : List Value) :
    wp m shlBody (Returns (.i64 (a <<< (b.toUInt64 % 64)) :: vs) (framePost st))
      st ⟨[.i64 a, .i32 b], [], vs⟩ env := by
  unfold shlBody Returns framePost
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, shl_seq, wp_ret_cons]
  simp

end Wasm.RustStd.U64
