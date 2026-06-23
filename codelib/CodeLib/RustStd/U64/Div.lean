import CodeLib.RustStd.U64.Basic

/-! `u64::div` (`a / b`) — reusable pieces for the zero-divisor guard and `i64.div_u`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- Local-read chunk for the bare `i64.div_u`, after a caller has established
that the divisor is nonzero. -/
theorem div_chunk :
    HBinChunkWhere (A := UInt64) (B := UInt64) (C := UInt64)
      [.divUI64] (· / ·) (fun _ b => b ≠ 0) := by
  intro α m env Q st P L rest i j a b vs ha hb hne
  simp only [toV_u64] at ha hb
  have hb' : (⟨P, L, .i64 a :: vs⟩ : Locals).get j = some (.i64 b) := by
    simpa [Locals.get] using hb
  simp only [List.cons_append, List.nil_append, toV_u64, wp_localGet_cons, ha, hb',
    wp_divUI64_cons, hne, ↓reduceIte]

/-- Stack convenience theorem for inlined proof sites after the guard has loaded operands. -/
theorem div_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a b : UInt64) (vs : List Value)
    (hb : b ≠ 0) :
    wp m (.divUI64 :: rest) Q st ⟨P, L, .i64 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a / b) :: vs⟩ env := by
  simp only [wp_divUI64_cons, hb, ↓reduceIte]

/-- Guarded divide body fragment, parameterized by dividend/divisor locals. The
panic tail emitted after the block is deliberately not part of this reusable
fragment. -/
abbrev divCheckedBody (i j : Nat) : Program :=
  [.block 0 0 (nonzeroGuard j ++ [.localGet i, .localGet j] ++ [.divUI64, .ret])]

set_option maxRecDepth 4096 in
/-- Checked divide body theorem for any dividend/divisor local pair. -/
theorem divBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i j : Nat) (a b : UInt64) (vs : List Value) (tail : Program)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (.i64 a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (.i64 b))
    (hne : b ≠ 0) :
    wp m (divCheckedBody i j ++ tail) (Returns (.i64 (a / b) :: vs) (framePost st))
      st ⟨P, L, vs⟩ env := by
  unfold divCheckedBody Returns framePost
  apply wp_block_cons
  change wp m
    (nonzeroGuard j ++ [.localGet i, .localGet j] ++ [.divUI64, .ret])
    _ st ⟨P, L, vs⟩ env
  rw [List.append_assoc (nonzeroGuard j) [.localGet i, .localGet j] [.divUI64, .ret]]
  rw [nonzeroGuardWp j b vs hb hne]
  change wp m ([.localGet i, .localGet j] ++ [.divUI64] ++ [.ret])
    _ st ⟨P, L, vs⟩ env
  rw [div_chunk i j a b vs ha hb hne]
  simp

end Wasm.RustStd.U64
