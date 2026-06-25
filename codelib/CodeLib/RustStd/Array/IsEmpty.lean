import CodeLib.RustStd.Array.Basic

/-! `&[T]::is_empty` — a zero-length test masked to a Rust bool, computed from the
slice length component. The reusable unit is the length-only chunk for the
fragment `[.const 0, .eq, .const 1, .and]`; it feeds both the inlined fragment
(`isEmpty_seq`) and the called body (`isEmptyBodyWp`) through the slice trunk. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- The `i32` result encoding emitted for `xs.is_empty()`: `1` when empty, else
`0`. -/
abbrev isEmptyValue (len : UInt32) : UInt32 :=
  if len = 0 then 1 else 0

/-- The extra `& 1` a caller emits after a bool-returning `is_empty` call is a
no-op on the canonical result (it is already `0`/`1`). The caller's fragment is
`… ; .const 1 ; .and` (i.e. `result &&& 1`); stated here as `1 &&& …` since `&&&`
commutes and `wp_and_cons` normalises the operand order. Reused at call sites
where Rust re-masks the returned bool. -/
theorem isEmptyValue_and_one (len : UInt32) :
    1 &&& isEmptyValue len = isEmptyValue len := by
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- The reusable chunk: with the slice length on the stack, the fragment
`[.const 0, .eq, .const 1, .and]` computes `isEmptyValue len`. Feeds the called
body via the trunk's `lenOpBodyWp`; also restated as `isEmpty_seq` for `rw`/`simp`
at an inlined `is_empty`. -/
theorem isEmpty_chunk : LenChunk [.const 0, .eq, .const 1, .and] isEmptyValue := by
  intro α m env Q st P L rest len vs
  simp only [List.cons_append, List.nil_append, wp_const_cons, wp_eq_cons, wp_and_cons]
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- Stack-form restatement of `isEmpty_chunk` for `rw`/`simp` at an inlined
`is_empty` once the length is on the stack (the `localGet` that pushes it is
handled by `wp_localGet_cons`, exactly as the integer `*_seq` lemmas are used).
At opt-0 the compiler emits `is_empty` as a *call* (so this crate's tests reuse
`isEmptyBodyWp`, the called shape); this restatement is the inline half of the
dual-shape API, for client code or hand-written wasm where the fragment is
inlined. -/
theorem isEmpty_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program} (len : UInt32) (vs : List Value) :
    wp m (.const 0 :: .eq :: .const 1 :: .and :: rest) Q st ⟨P, L, .i32 len :: vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 (isEmptyValue len) :: vs⟩ env := by
  simpa only [List.cons_append, List.nil_append]
    using isEmpty_chunk (rest := rest) len vs

/-- Function-body theorem for the generated `&[T]::is_empty` primitive body
`[localGet i, .const 0, .eq, .const 1, .and, .ret]`, reusing the slice trunk's
`lenOpBodyWp` with `isEmpty_chunk`. Serves the *called* shape; the *inlined*
shape uses `isEmpty_seq`. -/
theorem isEmptyBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m [.localGet i, .const 0, .eq, .const 1, .and, .ret]
      (Returns (.i32 (isEmptyValue len) :: vs) (framePost st)) st ⟨P, L, vs⟩ env :=
  lenOpBodyWp isEmpty_chunk st i len vs hlen

end Wasm.RustStd.Array
