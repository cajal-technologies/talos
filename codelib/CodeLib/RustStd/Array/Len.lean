import CodeLib.RustStd.Array.Basic

/-! `&[T]::len` — the slice length is the `i32` length component of the fat
pointer; the monomorphized primitive body just returns it. The reusable unit is
the degenerate length-only chunk (`frag = []`, `op = id`), which feeds both the
inlined read and the called body through the slice trunk. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- The reusable chunk: with the length on the stack, the empty fragment leaves
it unchanged — `len` is the identity length-only op. The `frag = []`, `op = id`
case of `LenChunk`; feeds `lenBodyWp` via the trunk's `lenOpBodyWp`. -/
theorem len_chunk : LenChunk [] (id : UInt32 → UInt32) := by
  intro α m env Q st P L rest len vs
  simp

/-- Inlined slice `len`: a single `localGet` of the length component. A
length-only op with an empty fragment has no stack transform, so the reusable
content is exactly `wp_localGet_cons`; this names it in slice vocabulary for
client proofs (and keeps `len`'s inline form symmetric with `is_empty`'s). -/
theorem len_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program}
    (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m (.localGet i :: rest) Q st ⟨P, L, vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 len :: vs⟩ env := by
  simp only [wp_localGet_cons, hlen]

/-- Function-body theorem for the generated `&[T]::len` primitive body
`[localGet i, .ret]`, reusing the slice trunk's `lenOpBodyWp` with `len_chunk`.
Serves the *called* shape; the *inlined* shape uses `len_seq`. -/
theorem lenBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m [.localGet i, .ret]
      (Returns (.i32 len :: vs) (framePost st)) st ⟨P, L, vs⟩ env :=
  lenOpBodyWp len_chunk st i len vs hlen

end Wasm.RustStd.Array
