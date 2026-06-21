import CodeLib.RustStd.U64.Basic

/-! `u64::rem` (`a % b`) — inlined as a zero-divisor guard `block` around `i64.rem_u`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The bare `i64.rem_u` chunk on stack operands, divisor ≠ 0. -/
theorem rem_chunk {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value)
    (hb : b ≠ 0) :
    wp m (.remUI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a % b) :: vs⟩ env := by
  simp only [wp_remUI64_cons, hb, ↓reduceIte]

/-- Verbatim opt-0 body of `rust_u64::rem`. -/
def remBody : Program :=
  [ .block 0 0 [ .localGet 1, .constI64 0, .eqI64, .const 1, .and, .br_if 0,
                 .localGet 0, .localGet 1, .remUI64, .ret ],
    .const 1048616, .call 67, .unreachable ]

set_option maxRecDepth 4096 in
/-- Export-body theorem for `rust_u64::rem` (divisor ≠ 0): peel the guard, then
**reuse `rem_chunk`** for the remainder (the `remUI64` atomic is excluded). -/
theorem remBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    (a b : UInt64) (vs : List Value) (hb : b ≠ 0) :
    wp m remBody (Returns (.i64 (a % b) :: vs) (framePost st)) st ⟨[.i64 a, .i64 b], [], vs⟩ env := by
  unfold remBody Returns framePost
  apply wp_block_cons
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [wp_localGet_cons, Locals.get, List.length_cons, List.length_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Nat.reduceAdd, Nat.reduceLT,
    reduceIte, wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons,
    wp_and_cons, wp_br_if_cons, h10]
  rw [rem_chunk a b _ hb]
  simp

end Wasm.RustStd.U64
