import HexEncodeStdio.TotalWrite
open Wasm Iris Iris.BI Iris.ProgramLogic Language.Notation Iris.Std
open Wasm.SepLogic Wasm.SmallStep
#check twp_globalGet
#check twp_sub
#check hdtwp_returnFromCallFallthrough
#check Submission.TotalIterator.hdtwp_returnFromCallFallthrough'
#check UInt32.add_ofNat_toNat_noWrap
#check pointsToBytes_nil
