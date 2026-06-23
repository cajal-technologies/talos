import CodeLib.RustStd.UInt

/-! `&[T]::len` — the slice length is the second `i32` in the fat pointer. -/

namespace Wasm.RustStd.Array

open Wasm Wasm.RustStd

/-- Local-read chunk theorem for an inlined slice `len`. -/
theorem len_seq {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program}
    (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m (.localGet i :: rest) Q st ⟨P, L, vs⟩ env ↔
      wp m rest Q st ⟨P, L, .i32 len :: vs⟩ env := by
  simp only [wp_localGet_cons, hlen]

set_option maxRecDepth 4096 in
/-- Function-body theorem for the generated `rust_array::len` primitive body. -/
theorem lenBodyWp {α} {m : Module} {env : HostEnv α} (st : Store α)
    {P L : List Value} (i : Nat) (len : UInt32) (vs : List Value)
    (hlen : (⟨P, L, vs⟩ : Locals).get i = some (.i32 len)) :
    wp m [.localGet i, .ret]
      (Returns (.i32 len :: vs) (framePost st)) st ⟨P, L, vs⟩ env := by
  unfold Returns framePost
  rw [len_seq i len vs hlen]
  simp

end Wasm.RustStd.Array
