import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.Entry
import CodeLib.UInt32
import CodeLib.UInt64
import CodeLib.RustStd.Frame
import CodeLib.RustStd.UInt
import CodeLib.RustStd.U64.Basic
import CodeLib.RustStd.U64.AbsDiff
import CodeLib.RustStd.U64.Add
import CodeLib.RustStd.U64.Sub
import CodeLib.RustStd.U64.Mul
import CodeLib.RustStd.U64.Div
import CodeLib.RustStd.U64.Rem
import CodeLib.RustStd.U64.BitAnd
import CodeLib.RustStd.U64.BitOr
import CodeLib.RustStd.U64.BitXor
import CodeLib.RustStd.U64.Not
import CodeLib.RustStd.U64.Shl
import CodeLib.RustStd.U64.Shr
import CodeLib.RustStd.Array.Basic
import CodeLib.RustStd.Array.Len
import CodeLib.RustStd.Array.IsEmpty
import CodeLib.RustStd.Option
import CodeLib.Near.State
import CodeLib.Near.Env
import CodeLib.Near.Proof

/-!
# CodeLib — umbrella import for downstream code

Generated `Program.lean` files (emitted by `lake exe verifier check`) and
hand-written `Spec.lean` siblings should `import CodeLib`, never the
interpreter directly. Today this is mostly a thin re-export of Wasm;
domain-specific spec helpers will live here as they accrete.
-/
