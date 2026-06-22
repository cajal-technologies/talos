import CodeLib.RustStd.U64.Basic

/-! `u64::shr` (`a >> b`, `b : u32`) — inlined as the mask-extend-shift sequence
`const 63; and; extendUI32; shrUI64`, a logical shift by `b % 64`.

`shr_seq` is the reusable chunk theorem (see `Shl.lean` for the design notes);
the *same* theorem discharges an inlined `a >> b` and the called export body
`shrBodyWp`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- Chunk theorem: the inlined `const 63; and; extendUI32; shrUI64` sequence, run
on `i32 b :: i64 a` operands, computes `a >>> (b % 64)`. Reuse this wherever
`a >> b` is inlined. -/
theorem shr_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (b : UInt32)
    (vs : List Value) :
    wp m (.const 63 :: .and :: .extendUI32 :: .shrUI64 :: rest) Q st
        ⟨P, L, .i32 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a >>> (b.toUInt64 % 64)) :: vs⟩ env := by
  have hamt : a >>> (UInt64.ofNat (63 &&& b).toNat % 64) = a >>> (b.toUInt64 % 64) := by
    simp; bv_decide
  simp only [wp_const_cons, wp_and_cons, wp_extendUI32_cons, wp_shrUI64_cons, hamt]

/-- Verbatim opt-0 body of `rust_u64::shr`. -/
def shrBody : Program :=
  [ .localGet 0, .localGet 1, .const 63, .and, .extendUI32, .shrUI64, .ret ]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::shr`, built by **reusing** `shr_seq`. -/
theorem shrBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a : UInt64) (b : UInt32) (vs : List Value) :
    wp m shrBody (Returns (.i64 (a >>> (b.toUInt64 % 64)) :: vs) (framePost st))
      st ⟨[.i64 a, .i32 b], [], vs⟩ env := by
  unfold shrBody Returns framePost
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, shr_seq, wp_ret_cons]
  simp

end Wasm.RustStd.U64
