import HexDecodeStdio.DecodePairOperational

open Wasm Wasm.SmallStep Project.HexStdio

#check Step.call
#check Step.block
#check Step.localGet
#check Step.load32
#check Step.store32
#check Step.load8U
#check Step.store8
#check Step.returnFromCallFallthrough
#check Step.brIf
#check Step.brIfZero
#check Step.exitControl
#check Mem.read32_write32_eq
#check Mem.read32_write32_disjoint
#check Mem.read8_write8_eq
#check Mem.read8_write8_ne
#check Mem.read8_write32_of_lt
#check Mem.write32_write32
#check Mem.write8_write8
#check UInt32.toNat_sub
#check UInt32.toNat_sub_of_le
#check UInt32.sub_toNat_of_le
#check Mem.read8_write32_of_lt
#check Mem.read8_write32_disjoint
#check Mem.read8_write32
#eval IO.println (repr Project.HexStdio.func14)

example (f : Nat → Nat) (n : Nat) (h : f 0 = n) (hn : 2 ≤ n) :
    f 0 ≠ 0 := by
  rw (occs := .pos [1]) [h]
  trace_state
  omega
