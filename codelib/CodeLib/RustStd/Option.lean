import Interpreter.Wasm

/-!
# `CodeLib.RustStd.Option`

Shared helpers for reasoning about the C-ABI `Option<i64>` encoding.

Staged ahead of its first consumer: no crate in `programs/rust` uses this yet.
It is here because the corpus roadmap reaches `Option`-returning std methods
(`unwrap_or`, `is_some`, `map`) and the `checked_*` arithmetic family, all of
which return an `Option` across an `extern "C"` boundary and so hit exactly this
sentinel encoding.

The convention is:

* `None` is encoded as the sentinel `i64::MIN` (i.e. `0x8000_0000_0000_0000`).
* `Some(x)` is encoded as `x` itself.

This encoding conflates `Some(i64::MIN)` with `None`; the `Option`-level
lifts here therefore assume the value is `≠ some Int64.minValue`. Specs
at the raw `UInt64` level have no such caveat.
-/

namespace Wasm.RustStd.Option

/-- The Wasm-level sentinel that encodes `None` (= `i64::MIN` reinterpreted
as `UInt64` = `2 ^ 63`). -/
def sentinel : UInt64 := 0x8000000000000000

@[simp] theorem sentinel_eq : sentinel = (9223372036854775808 : UInt64) := rfl

/-- `i64::MIN` reinterpreted as `UInt64` is exactly the sentinel. -/
theorem minValue_toUInt64 : (Int64.minValue : Int64).toUInt64 = sentinel := rfl

/-- Encode an abstract `Option Int64` into the wasm `UInt64` representation. -/
def encode : Option Int64 → UInt64
  | none   => sentinel
  | some x => x.toUInt64

@[simp] theorem encode_none : encode none = sentinel := rfl
@[simp] theorem encode_some (x : Int64) : encode (some x) = x.toUInt64 := rfl

/-- `Int64.toUInt64` is injective (recover the input via `toInt64`). -/
theorem toUInt64_injective : Function.Injective Int64.toUInt64 := by
  intro a b h
  have := congrArg UInt64.toInt64 h
  simpa [Int64.toInt64_toUInt64] using this

/-- For `o ≠ some Int64.minValue`, the encoded value distinguishes `Some`
from `None` via inequality with the sentinel. -/
theorem encode_ne_sentinel_of_some {x : Int64} (hx : x ≠ Int64.minValue) :
    encode (some x) ≠ sentinel := by
  intro h
  apply hx
  apply toUInt64_injective
  show x.toUInt64 = (Int64.minValue : Int64).toUInt64
  rw [minValue_toUInt64]; exact h

/-- `encode o = sentinel` iff `o ∈ {none, some Int64.minValue}`. -/
theorem encode_eq_sentinel_iff (o : Option Int64) :
    encode o = sentinel ↔ o = none ∨ o = some Int64.minValue := by
  cases o with
  | none => simp
  | some x =>
    constructor
    · intro h
      right
      have hx : x.toUInt64 = (Int64.minValue : Int64).toUInt64 := by
        rw [minValue_toUInt64]; exact h
      exact congrArg some (toUInt64_injective hx)
    · rintro (h | h)
      · cases h
      · cases h; rfl

end Wasm.RustStd.Option
