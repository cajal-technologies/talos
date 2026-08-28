import HexDecodeStdio.DecodeLoopOperational

open Wasm Project.HexStdio

#eval IO.println (repr func5)
#eval IO.println "AFTER_LOOP"
#eval IO.println (repr Project.HexDecodeStdio.decodeCoreAfterLoop)
#eval IO.println "AFTER_CORE"
#eval IO.println (repr Project.HexDecodeStdio.decodeAfterCore)
#eval IO.println "WRITE_ALL"
#eval IO.println (repr func8)
