import Project.HexStdio.Program

namespace Project.HexDecodeStdio

open Wasm Project.HexStdio

/-- The continuation of `read_to_end` after its first `read_chunk` call. -/
def readToEndAfterFirstRead : Program := func7.drop 21

theorem func7_first_read_split :
    func7 =
      [.globalGet 0, .const 32, .sub, .localTee 1, .globalSet 0,
        .localGet 1, .const 0, .store32 12,
        .localGet 1, .constI64 4294967296, .store64 4,
        .localGet 1, .const 16, .add,
        .localGet 1, .const 31, .add,
        .localGet 1, .const 4, .add, .call 4] ++
        readToEndAfterFirstRead := by
  rfl

end Project.HexDecodeStdio
