import CodeLib.RustStd.U64.Basic

/-! `u64::bitxor` — inlined to a single `i64.xor`. Chunk fact proved by `bin_chunk_of`,
reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable chunk: `[.xorI64]` computes `^^^` on stack operands. -/
theorem bitxor_chunk :
    BinChunk [.xorI64] ((· ^^^ ·) : UInt64 → UInt64 → UInt64) := by
  bin_chunk_of Wasm.SmallStep.wp_xorI64

end Wasm.RustStd.U64
