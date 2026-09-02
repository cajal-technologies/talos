import HexDecodeStdio.DecodeLoopRecursive
namespace Project.HexDecodeStdio
open Wasm Project.HexStdio
example (off : Nat) (h : 1048492 ≤ off) :
    (coreFrame + 56).toNat + 4 ≤ off := by
  norm_num [UInt32.toNat_add, UInt32.size]
  omega
example (off : Nat) (h : 1048492 ≤ off) : coreError.toNat + 4 ≤ off := by
  norm_num [UInt32.size]
  omega
end Project.HexDecodeStdio

example (n : Nat) (h : n % 2 = 0) : (UInt32.ofNat n &&& 1) = 0 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_and]
#check Wasm.read32_write64_low
#check Wasm.read32_write64_high
#check Wasm.read64_low
#check Wasm.read64_high
