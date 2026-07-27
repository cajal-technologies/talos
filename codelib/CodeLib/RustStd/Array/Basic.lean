import CodeLib.RustStd.UInt

/-!
# Rust slice ABI

A `wasm32` Rust slice crosses the C ABI as two adjacent `i32` words: its data
pointer followed by its element count.  The former custom-WP loader and
fuel-bounded callee bridges have been removed; `Array.SmallStep` provides the
authoritative iris-lean loader over this physical layout.
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

end Wasm.RustStd.Array
