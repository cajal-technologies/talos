import CodeLib.RustStd.U64.Basic

/-! `u64::shl` (`a << b`, `b : u32`) — inlined as the shared mask-extend-shift
prefix followed by `shlI64`, a shift by `b % 64`. The `b % 64` normalisation is
the trunk-level `shiftAmount_norm` (shared with `shr`), so there is no
`bv_decide` in this file. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable chunk for `a << b` (heterogeneous: `a : u64`, `b : u32`): the
mask-extend-shift sequence on stack operands, normalising the count via
`shiftAmount_norm`. -/
theorem shl_chunk :
    BinChunk (A := UInt64) (B := UInt32) (C := UInt64)
      (shiftAmountFrag ++ [.shlI64]) (fun a b => a <<< (b.toUInt64 % 64)) := by
  shift_chunk_of Wasm.SmallStep.wp_shlI64

end Wasm.RustStd.U64
