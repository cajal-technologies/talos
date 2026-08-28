import HexEncodeStdio.TotalWrite
open Wasm Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep
#check twp_globalGet
#check twp_sub
#check twp_returnFromCallFallthrough
#check Project.HexEncodeStdio.TotalIterator.twp_returnFromCallFallthrough'
#check UInt32.add_ofNat_toNat_noWrap
#check pointsToBytes_nil
