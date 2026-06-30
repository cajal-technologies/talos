import CodeLib.RustStd.Array.Basic

/-! `&[T]::is_empty` — a zero-length test masked to a Rust bool, computed from the
slice length component. The reusable unit is the unary chunk (a `UnChunk` over
`UInt32`) for the fragment `[.const 0, .eq, .const 1, .and]`; the called body
(`isEmptyBodyWp`) derives from it through the integer trunk's `unBodyReturnsWp`,
and an inlined occurrence reuses the chunk directly. -/

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
`[.const 0, .eq, .const 1, .and]` computes `isEmptyValue len`. The single
stack-form unit for `is_empty` (a `UnChunk` over `UInt32`): it feeds the called
body via the trunk's `unBodyReturnsWp`, and is `rw`-able directly at an inlined
`is_empty` once the length is on the stack. -/
theorem isEmpty_chunk : UnChunk (T := UInt32) [.const 0, .eq, .const 1, .and] isEmptyValue := by
  intro α m env Q st P L rest len vs
  simp only [toV_u32, List.cons_append, List.nil_append, wp_const_cons, wp_eq_cons, wp_and_cons]
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- Function-body theorem for the generated `&[T]::is_empty` primitive body
`[localGet i, .const 0, .eq, .const 1, .and, .ret]`, reusing the integer trunk's
`unBodyReturnsWp` with `isEmpty_chunk`. This is the *called* shape; an inlined
`is_empty` reuses `isEmpty_chunk` directly (opt-0 only ever emits the call). -/
theorem isEmptyBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m [.localGet i, .const 0, .eq, .const 1, .and, .ret]
      (Returns (.i32 (isEmptyValue len) :: vs) (framePost st)) st ⟨P, L, vs⟩ env :=
  unBodyReturnsWp isEmpty_chunk st i len vs hlen

end Wasm.RustStd.Array
