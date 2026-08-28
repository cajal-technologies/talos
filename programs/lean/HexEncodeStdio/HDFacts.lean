import HexEncodeStdio.HDMemoryBytes

namespace Project.HexEncodeStdio

open Wasm

structure Offset32Facts (base offset : UInt32) : Prop where
  noWrap : (base + offset).toNat = base.toNat + offset.toNat
  one : ((base + offset) + 1).toNat = (base + offset).toNat + 1
  two : ((base + offset) + 2).toNat = (base + offset).toNat + 2
  three : ((base + offset) + 3).toNat = (base + offset).toNat + 3

structure Address64Facts (address : UInt32) : Prop where
  one : (address + 1).toNat = address.toNat + 1
  two : (address + 2).toNat = address.toNat + 2
  three : (address + 3).toNat = address.toNat + 3
  four : (address + 4).toNat = address.toNat + 4
  five : (address + 5).toNat = address.toNat + 5
  six : (address + 6).toNat = address.toNat + 6
  seven : (address + 7).toNat = address.toNat + 7

end Project.HexEncodeStdio
