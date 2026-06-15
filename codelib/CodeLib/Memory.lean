import Interpreter.Wasm

namespace Wasm

-- grow only updates `pages`; the byte function is unchanged at every address
theorem Mem.grow_preserves {m mem' : Mem} {delta : UInt32} {cap cur : Nat}
    (h : m.grow delta cap = some (mem', cur)) (i : Nat) :
    mem'.bytes i = m.bytes i := by
  simp only [Mem.grow] at h
  split_ifs at h with hle
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    rfl
  · simp at h

theorem Mem.grow_read8 {m mem' : Mem} {delta : UInt32} {cap cur : Nat}
    (h : m.grow delta cap = some (mem', cur)) (a : UInt32) :
    mem'.read8 a = m.read8 a := by
  simp only [Mem.read8, Mem.grow_preserves h]

-- after writeBytesFrom, address dst+k carries src[srcOff+k] for k < len
theorem Mem.data_segment_initialized {m : Mem} {dst srcOff len : Nat} {src : List UInt8}
    {k : Nat} (hk : k < len) (hsrc : srcOff + k < src.length) :
    (m.writeBytesFrom dst src srcOff len).bytes (dst + k) =
    src[srcOff + k]'(by omega) := by
  simp only [Mem.writeBytesFrom]
  rw [if_pos ⟨by omega, by omega⟩,
      Nat.add_sub_cancel_left,
      getElem?_pos src (srcOff + k) hsrc,
      Option.getD_some]

theorem Mem.data_segment_initialized_read8 {m : Mem} {dst srcOff len : Nat} {src : List UInt8}
    {a : UInt32} {k : Nat} (ha : a.toNat = dst + k)
    (hk : k < len) (hsrc : srcOff + k < src.length) :
    (m.writeBytesFrom dst src srcOff len).read8 a =
    src[srcOff + k]'(by omega) := by
  simp only [Mem.read8]
  rw [ha]
  exact Mem.data_segment_initialized hk hsrc

end Wasm
