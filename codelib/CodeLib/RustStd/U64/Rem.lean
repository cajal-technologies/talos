import CodeLib.RustStd.U64.Basic

/-! `u64::rem` (`a % b`) — a zero-divisor guard `block` around `i64.rem_u`,
reusing the trunk's `checkedBinBodyReturnsWp` template. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- The reusable chunk for the bare `i64.rem_u`, carrying the nonzero-divisor
precondition. -/
theorem rem_chunk :
    BinChunk (A := UInt64) (B := UInt64) (C := UInt64)
      [.remUI64] (· % ·) (fun _ b => b ≠ 0) := by
  intro α m env Q st P L rest a b vs hne
  simp only [List.cons_append, List.nil_append, toV_u64, wp_remUI64_cons, hne, ↓reduceIte]

/-- Concrete restatement of `rem_chunk` for `rw`/`simp` at an inlined `i64.rem_u`
once the guard has loaded operands. -/
theorem rem_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value)
    (hb : b ≠ 0) :
    wp m (.remUI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a % b) :: vs⟩ env := by
  simpa only [toV_u64, List.cons_append, List.nil_append]
    using rem_chunk (rest := rest) a b vs hb

set_option maxRecDepth 4096 in
/-- Checked remainder body for any dividend/divisor local pair, reusing the
trunk's guarded-body template with the `nonzeroGuard` fall-through. The panic
`tail` is arbitrary (unreachable when `b ≠ 0`). -/
theorem remBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i j : Nat) (a b : UInt64) (vs : List Value) (tail : Program)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (.i64 a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (.i64 b))
    (hne : b ≠ 0) :
    wp m (checkedBinBody (nonzeroGuard j) [.remUI64] i j ++ tail)
      (Returns (.i64 (a % b) :: vs) (framePost st))
      st ⟨P, L, vs⟩ env :=
  checkedBinBodyReturnsWp rem_chunk st i j a b vs tail
    (fun {_Q _rest} => nonzeroGuardWp j b vs hb hne) ha hb hne

end Wasm.RustStd.U64
