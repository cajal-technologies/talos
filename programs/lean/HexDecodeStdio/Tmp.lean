import HexDecodeStdio.DecodeLoopRecursive
namespace Project.HexDecodeStdio
open Wasm Project.HexStdio
example (off : Nat) (h : 1048492 ≤ off) :
    (coreFrame + 56).toNat + 4 ≤ off := by
  change 1048492 ≤ off
  exact h
example (off : Nat) (h : 1048492 ≤ off) : coreError.toNat + 4 ≤ off := by
  change 1048468 ≤ off
  omega
end Project.HexDecodeStdio

example (n : Nat) (h : n % 2 = 0) : (UInt32.ofNat n &&& 1) = 0 := by
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_and, Nat.and_one_is_mod, Nat.mod_mod_of_dvd, h]
