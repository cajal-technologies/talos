import CodeLib.RustStd.Array.Basic

/-! `&[T]::len` — the slice length is the `i32` length component of the fat
pointer; the monomorphized primitive body just returns it. The reusable unit is
the degenerate unary chunk (`frag = []`, `op = id`) over the length, which feeds
the called body through the integer trunk's `unBodyReturnsWp`. The *inlined*
read is just `wp_localGet_cons`, so it needs no slice-specific lemma. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- The reusable chunk: with the length on the stack, the empty fragment leaves
it unchanged — `len` is the identity length-only op. The `frag = []`, `op = id`
case of the trunk's `UnChunk` (at `UInt32`, whose `toV` is `.i32`); feeds
`lenBodyWp` via `unBodyReturnsWp`. -/
theorem len_chunk : UnChunk (T := UInt32) [] (id : UInt32 → UInt32) := by
  intro α m env Q st P L rest len vs
  simp

/-- Function-body theorem for the generated `&[T]::len` primitive body
`[localGet i, .ret]`, reusing the integer trunk's `unBodyReturnsWp` with
`len_chunk`. Serves the *called* shape; the *inlined* shape is just
`wp_localGet_cons`. -/
theorem lenBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m [.localGet i, .ret]
      (Returns (.i32 len :: vs) (framePost st)) st ⟨P, L, vs⟩ env :=
  unBodyReturnsWp len_chunk st i len vs hlen

end Wasm.RustStd.Array
