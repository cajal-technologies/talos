import CodeLib.RustStd.U64.Basic

/-! `u64::div` (`a / b`) — inlined as a zero-divisor guard `block` around `i64.div_u`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The bare `i64.div_u` chunk on stack operands, divisor ≠ 0 (reusable wherever
the divide itself is inlined, once the guard is peeled). -/
theorem div_chunk {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value)
    (hb : b ≠ 0) :
    wp m (.divUI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a / b) :: vs⟩ env := by
  simp only [wp_divUI64_cons, hb, ↓reduceIte]

/-- Verbatim opt-0 body of `rust_u64::div`. -/
def divBody : Program :=
  [ .block 0 0 [ .localGet 1, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
                 .localGet 0, .localGet 1, .divUI64, .ret ],
    .const 1048600, .call 66, .unreachable ]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::div` (divisor ≠ 0): peel the zero-divisor
guard `block`, then **reuse `div_chunk`** for the divide itself (the `divUI64`
atomic is excluded from the guard reduction so the chunk is the only path). -/
theorem divBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) (hb : b ≠ 0) :
    wp m divBody (Returns (.i64 (a / b) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold divBody Returns framePost
  apply wp_block_cons
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons,
    wp_and_cons, wp_br_if_cons, h10]
  rw [div_chunk a b _ hb]
  simp

end Wasm.RustStd.U64
