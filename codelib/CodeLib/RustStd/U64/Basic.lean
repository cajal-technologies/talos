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

end Wasm.RustStd
