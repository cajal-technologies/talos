import CodeLib.RustStd.UInt

/-! `&[T]::is_empty` — emitted as a zero-length test masked to a Rust bool. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- The `i32` result encoding emitted for `xs.is_empty()`. -/
abbrev isEmptyValue (len : UInt32) : UInt32 :=
  if len = 0 then 1 else 0

/-- The extra `& 1` that Rust often emits after a bool-returning call is a no-op
for the canonical `is_empty` result. -/
theorem isEmptyValue_and_one (len : UInt32) :
    1 &&& isEmptyValue len = isEmptyValue len := by
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

/-- Local-read chunk theorem for an inlined slice `is_empty`. -/
theorem isEmpty_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program}
    (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m (.localGet i :: .const 0 :: .eq :: .const 1 :: .and :: rest)
        Q st ⟨P, L, vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 (isEmptyValue len) :: vs⟩ env := by
  simp only [wp_localGet_cons, hlen, wp_const_cons, wp_eq_cons, wp_and_cons]
  unfold isEmptyValue
  by_cases h : len = 0 <;> simp [h]

set_option maxRecDepth 4096 in
/-- Function-body theorem for the generated `rust_array::is_empty` primitive body. -/
theorem isEmptyBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m [.localGet i, .const 0, .eq, .const 1, .and, .ret]
      (Returns (.i32 (isEmptyValue len) :: vs) (framePost st)) st ⟨P, L, vs⟩ env := by
  unfold Returns framePost
  rw [isEmpty_seq i len vs hlen]
  simp

end Wasm.RustStd.Array
