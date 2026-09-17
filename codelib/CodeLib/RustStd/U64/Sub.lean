import CodeLib.RustStd.U64.Basic

/-! `u64::sub` — inlined to a single `i64.sub`. Chunk fact proved by `bin_chunk_of`,
reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable chunk: `[.subI64]` computes `-` on stack operands. -/
theorem sub_chunk :
    BinChunk [.subI64] ((· - ·) : UInt64 → UInt64 → UInt64) := by
  bin_chunk_of Wasm.SmallStep.wp_subI64

end Wasm.RustStd.U64
