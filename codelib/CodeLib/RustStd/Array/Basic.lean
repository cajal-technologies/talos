import Interpreter.Wasm

/-!
# Rust slice ABI

A `wasm32` Rust slice crosses the C ABI as two adjacent `i32` words: its data
pointer followed by its element count. `FatPtrAt` states that layout;
`Array.SmallStep` provides the small-step loader over it. `isEmptyValue` is the
canonical `0`/`1` result of `<[T]>::is_empty`.
-/

namespace Wasm.RustStd.Array

open Wasm

/-- Physical `(dataPtr, len)` fat-pointer layout at address `p`. -/
structure FatPtrAt {α : Type} (st : Store α)
    (p dataPtr len : UInt32) : Prop where
  data : st.mem.read32 (p + 0) = dataPtr
  count : st.mem.read32 (p + 4) = len
  bound : p.toNat + 8 ≤ st.mem.pages * 65536
  noWrap : p.toNat + 8 ≤ 4294967296

/-- The value `<[T]>::is_empty` returns for a slice of length `len`. -/
abbrev isEmptyValue (len : UInt32) : UInt32 :=
  if len = 0 then 1 else 0

end Wasm.RustStd.Array
