import CodeLib.RustStd.U64.Basic

/-! `u64::shr` (`a >> b`, `b : u32`) — inlined as the shared mask-extend-shift
prefix followed by `shrUI64`, a logical shift by `b % 64`. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd

/-- Local-read chunk theorem for `a >> b`; the `b % 64` normalisation is baked in once here. -/
theorem shr_chunk :
    HBinChunk (A := UInt64) (B := UInt32) (C := UInt64)
      (shiftAmountFrag ++ [.shrUI64])
      (fun a b => a >>> (b.toUInt64 % 64)) := by
  intro α m env Q st P L rest i j a b vs ha hb
  simp only [toV_u64, toV_u32] at ha hb
  have hb' : (⟨P, L, .i64 a :: vs⟩ : Locals).get j = some (.i32 b) := by
    simpa [Locals.get] using hb
  have hamt : a >>> (UInt64.ofNat (shiftMask &&& b).toNat % 64) = a >>> (b.toUInt64 % 64) := by
    simp; bv_decide
  simp only [shiftAmountFrag, List.cons_append, List.nil_append, toV_u64, wp_localGet_cons,
    ha, hb', wp_const_cons, wp_and_cons, wp_extendUI32_cons, wp_shrUI64_cons, hamt]

/-- Stack convenience theorem for inlined proof sites that have already loaded operands. -/
theorem shr_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (a : UInt64) (b : UInt32)
    (vs : List Value) :
    wp m (.const shiftMask :: .and :: .extendUI32 :: .shrUI64 :: rest) Q st
        ⟨P, L, .i32 b :: .i64 a :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i64 (a >>> (b.toUInt64 % 64)) :: vs⟩ env := by
  have hamt : a >>> (UInt64.ofNat (shiftMask &&& b).toNat % 64) = a >>> (b.toUInt64 % 64) := by
    simp; bv_decide
  simp only [wp_const_cons, wp_and_cons, wp_extendUI32_cons, wp_shrUI64_cons, hamt]

/-- Fallthrough body theorem for `rust_u64::shr`, built by reusing `shr_chunk`. -/
theorem shrBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i j : Nat) (a : UInt64) (b : UInt32) (vs : List Value)
    (ha : (⟨P, L, vs⟩ : Locals).get i = some (.i64 a))
    (hb : (⟨P, L, vs⟩ : Locals).get j = some (.i32 b)) :
    wp m ([.localGet i, .localGet j] ++ shiftAmountFrag ++ [.shrUI64])
      (fun c => ∃ st',
        c = .Fallthrough st' ⟨P, L, .i64 (a >>> (b.toUInt64 % 64)) :: vs⟩ ∧
          framePost st st')
      st ⟨P, L, vs⟩ env :=
  hbinBodyWp shr_chunk st i j a b vs ha hb

end Wasm.RustStd.U64
