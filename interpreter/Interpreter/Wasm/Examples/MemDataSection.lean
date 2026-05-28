import Interpreter.Wasm.Wp.Tactic

/-! ## Example: data-section plumbing

    Smallest possible example exercising the new memory surface. The
    module declares one page of linear memory with a single `(data ...)`
    segment of four bytes at offset 0; the function body is a no-op that
    returns the constant 7. The interesting content is the *initial
    store*: `Module.initialStore` should fold the data segment into the
    memory, and `Mem.read32` at offset 0 should reassemble the four
    little-endian bytes into a `UInt32`.

    Load/store *instructions* are not yet wired up — that's the next
    milestone. Until then this example just pins down the plumbing.

    Bytes `[0x42, 0x43, 0x44, 0x45]` little-endian-decoded as a u32 give
    `0x45444342`. -/

namespace Wasm

def memModule : Module :=
  { funcs := [{ body := [.const 7], results := [.i32] }]
    memory := some
      { pagesMin := 1
        data := [{ offset := some 0, bytes := [0x42, 0x43, 0x44, 0x45] }] } }

theorem memDataSection_read32_zero :
    memModule.initialStore.mem.read32 0 = 0x45444342 := by
  native_decide

end Wasm
