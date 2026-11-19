import Interpreter.Wasm

/-!
# `Mem.readBytes` / `Mem.writeBytes` simp lemmas

Length and page-count rewrites and byte-lookup rules (inside, before and
after the written range) for the interpreter's byte-list memory accessors,
plus the little-endian `read32` of four freshly written bytes. They are global `@[simp]` lemmas: every proof that
imports `CodeLib` has them in its default simp set.
-/

namespace Wasm

@[simp] theorem Mem.readBytes_length (m : Mem) (off len : Nat) :
    (m.readBytes off len).length = len := by simp [Mem.readBytes]

@[simp] theorem Mem.writeBytes_pages (m : Mem) (off : Nat) (data : List UInt8) :
    (m.writeBytes off data).pages = m.pages := rfl

@[simp] theorem Mem.writeBytes_byte_in (m : Mem) (off i : Nat) (data : List UInt8)
    (h : i < data.length) :
    (m.writeBytes off data).bytes (off + i) = data[i] := by simp [Mem.writeBytes, h]

@[simp] theorem Mem.writeBytes_byte_before (m : Mem) (off i : Nat) (data : List UInt8)
    (h : i < off) :
    (m.writeBytes off data).bytes i = m.bytes i := by simp [Mem.writeBytes]; omega

@[simp] theorem Mem.writeBytes_byte_after (m : Mem) (off i : Nat) (data : List UInt8)
    (h : off + data.length ≤ i) :
    (m.writeBytes off data).bytes i = m.bytes i := by simp [Mem.writeBytes]; omega

@[simp] theorem Mem.read32_writeBytes_four (m : Mem) (a : UInt32) (b0 b1 b2 b3 : UInt8) :
    (m.writeBytes a.toNat [b0, b1, b2, b3]).read32 a =
      b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24) := by
  simp [Mem.read32, Mem.writeBytes]

end Wasm
