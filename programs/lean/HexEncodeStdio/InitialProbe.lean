import HexEncodeStdio.ReadToEndLoop

namespace Submission.HexDecodeStdio
open Wasm Project.HexStdio Project.HexStdio.Spec Wasm.SmallStep

set_option maxRecDepth 100000 in
example (input : List UInt8) :
    (encodeFrameStore input).wasm.mem.pages = 17 := by
  simp [encodeFrameStore, encodeInitialStore]
  decide

set_option maxRecDepth 100000 in
example (input : List UInt8) :
    (encodeFrameStore input).wasm.mem.read32 1053960 = 0 := by
  simp [encodeFrameStore, encodeInitialStore, Mem.read32]
  decide

set_option maxRecDepth 100000 in
example (input : List UInt8) :
    (encodeFrameStore input).wasm.mem.readBytes 1048576 16 =
      Submission.Hex.asciiTable := by
  simp [encodeFrameStore, encodeInitialStore, Mem.readBytes]
  decide

example (input : List UInt8) :
    (encodeFrameStore input).runtime.currentModule = «module» := by rfl

example (input : List UInt8) :
    (encodeFrameStore input).runtime.currentHost = Universal.envFor «module» := by rfl

example (input : List UInt8) :
    (encodeFrameStore input).wasm.memoryCap
      (encodeFrameStore input).runtime.currentModule 0 = 65536 := by rfl

end Submission.HexDecodeStdio
