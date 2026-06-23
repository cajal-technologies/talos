import CodeLib.RustStd.UInt

/-!
# `UInt64` as a wasm `i64`

The `UIntWasm UInt64` instance: a `u64` is carried as `Value.i64`. The trunk's
generic chunk/body helpers specialise to this instance; each operator's own
file (`U64/Add.lean`, …) supplies the concrete `i64.*` fragment.
-/

namespace Wasm.RustStd

open Wasm

instance instUIntWasmUInt64 : UIntWasm UInt64 where
  toV a := .i64 a

/-- `toV` on `UInt64` is `Value.i64` — a `@[simp]` rewrite so chunk proofs reduce
the stack to concrete `i64` and the atomic `wp_*` lemmas fire. -/
@[simp] theorem toV_u64 (a : UInt64) : (UIntWasm.toV a : Value) = .i64 a := rfl

namespace U64

/-- Wasm masks `u64` shift amounts to the low 6 bits. -/
abbrev shiftMask : UInt32 := 63

/-- The emitted mask-and-extend prefix shared by `u64` shifts whose count starts
as a Rust `u32`. -/
abbrev shiftAmountFrag : Program := [.const shiftMask, .and, .extendUI32]

/-- The emitted nonzero-divisor guard prefix used before unsigned division and
remainder. -/
abbrev nonzeroGuard (i : Nat) : Program :=
  [.localGet i, .constI64 0, .eqI64, .const 1, .and, .br_if 0]

/-- The opt-0 unsigned-division guard falls through unchanged when the divisor
local is a nonzero `u64`. -/
theorem nonzeroGuardWp {α : Type} {m : Module} {env : HostEnv α} {Q : Assertion α}
    {st : Store α} {P L : List Value} {rest : Program}
    (i : Nat) (b : UInt64) (vs : List Value)
    (hget : (⟨P, L, vs⟩ : Locals).get i = some (.i64 b)) (hb : b ≠ 0) :
    wp m (nonzeroGuard i ++ rest)
      Q st ⟨P, L, vs⟩ env ↔
    wp m rest Q st ⟨P, L, vs⟩ env := by
  have h10 : (1 : UInt32) &&& 0 = 0 := by decide
  simp only [nonzeroGuard, List.cons_append, List.nil_append, wp_localGet_cons, hget,
    wp_constI64_cons, wp_eqI64_cons, hb, ↓reduceIte, wp_const_cons, wp_and_cons,
    wp_br_if_cons, h10]

end U64

end Wasm.RustStd
