import CodeLib.Attrs
import CodeLib.Basic
import CodeLib.CostedSteps
import CodeLib.Entry
import CodeLib.Equivalence
import CodeLib.List
import CodeLib.StdioContract
import CodeLib.UInt32
import CodeLib.UInt64
import CodeLib.ByteReassembly
import CodeLib.MemBytes
import CodeLib.WordCodec
import CodeLib.WordCodec.UInt32
import CodeLib.WordCodec.UInt64
import CodeLib.RustStd.Frame
import CodeLib.RustStd.Region
import CodeLib.RustStd.MemArray
import CodeLib.RustStd.MemArray.SmallStep
import CodeLib.RustStd.U64.Basic
import CodeLib.RustStd.U64.AbsDiff
import CodeLib.RustStd.U64.AbsDiffTotal
import CodeLib.RustStd.Array.Basic
import CodeLib.RustStd.Array.SmallStep
import CodeLib.RustStd.Vec.Basic
import CodeLib.RustStd.Vec.Codec
import CodeLib.RustStd.Borsh
import CodeLib.RustStd.HashMap.Basic
import CodeLib.RustStd.HashMap.Codec
import CodeLib.SepLogic.IrisCompat
import CodeLib.SepLogic.Tactics
import CodeLib.SepLogic.WasmHeap
import CodeLib.SepLogic.WasmRules
import CodeLib.SepLogic.SmallStepLanguage
import CodeLib.SepLogic.SmallStepState
import CodeLib.SepLogic.SmallStepLifting
import CodeLib.SepLogic.SmallStepTotalLifting
import CodeLib.SepLogic.SmallStepTotalLiftingBytes
import CodeLib.SepLogic.SmallStepTotalLoop
import CodeLib.SepLogic.SmallStepGhostInit
import CodeLib.SepLogic.SmallStepAdequacy
import CodeLib.SepLogic.SmallStepOutcomeLanguage
import CodeLib.SepLogic.SmallStepOutcomeAdequacy
import CodeLib.Host.UniversalStdIO

/-!
# CodeLib — umbrella import for downstream code

Generated `Program.lean` files (emitted by `lake exe verifier check`, via
`CodeLib.Generated`) and hand-written `Spec.lean` siblings should
`import CodeLib`, never the interpreter directly.

This module re-exports the reasoning infrastructure only:

* `CodeLib.Basic` — the interpreter's public Wasm surface (`Interpreter.Wasm`);
* `Attrs` — the `@[spec_of]` / `@[proves]` attributes read by the verifier;
* small `UInt32` / `UInt64` / `List` / byte-reassembly lemmas, the
  `Mem.readBytes` / `Mem.writeBytes` simp lemmas (`MemBytes`) and the
  `WordCodec` little-endian codecs (`u32le`, `u64le`);
* `RustStd.*` — memory-region and array views (`Frame`, `Region`,
  `MemArray`), Rust ABI layouts (slices, `Vec`, Borsh) and the reusable
  `u64::abs_diff` body proof;
* `SepLogic.*` — the iris-lean program logic over `Wasm.SmallStep`: ghost
  resources, partial and total lifting rules, loop rules, ghost
  initialization, adequacy (plain and outcome-observing) and the proof-mode
  tactics;
* `Host.UniversalStdIO` — total rules for the universal host's stdio calls;
* `Entry` — bridges from a fuel-free `TerminatesWith` spec to a big-step
  `wp` goal on a function body; `Equivalence` — observational equivalence
  of two small-step configurations.

Worked examples and regression tests (`CodeLib.Examples.*`, the
`CodeLib.SepLogic.*Example*` modules, and `CodeLib.Host.StdIO`, the
positional-host helpers only those examples use) and the NEAR host
(`CodeLib.Near.*`) are deliberately **not** re-exported, so importing
`CodeLib` does not elaborate them; the codelib build still checks them as
lakefile roots. Import them by path where needed, as `CodeLib.IEEE32.Exec`
is for the float programs.
-/
