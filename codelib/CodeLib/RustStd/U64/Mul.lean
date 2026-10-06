import CodeLib.RustStd.U64.Basic

/-! `u64::mul` — inlined to a single `i64.mul`. Chunk fact proved by `bin_chunk_of`,
reusing the trunk. -/

namespace Wasm.RustStd.U64
open Wasm Wasm.RustStd
open Iris Iris.ProgramLogic Language.Notation

/-- The reusable chunk: `[.mulI64]` computes `*` on stack operands. -/
theorem mul_chunk :
    BinChunk [.mulI64] ((· * ·) : UInt64 → UInt64 → UInt64) := by
  bin_chunk_of Wasm.SmallStep.wp_mulI64

end Wasm.RustStd.U64
