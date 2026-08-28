import HexDecodeStdio.DecodeWrapperStatus

open Wasm Project.HexStdio Submission.HexDecodeStdio

#eval IO.println "SUCCESS_AFTER_ALLOC"
#eval IO.println (repr decodeSuccessAfterAlloc)
#eval IO.println "STATUS_BODY4_DROP1"
#eval IO.println (repr (decodeStatusBody4.drop 1))
#eval IO.println "AFTER_STATUS"
#eval IO.println (repr decodeAfterStatus)
#eval IO.println "SUCCESS_BLOCKS"
#eval IO.println (repr (decodeSuccessAfterAlloc.drop 9))
#eval IO.println "OUTER_BODY"
#eval IO.println (repr (firstBlockBody (decodeSuccessAfterAlloc.drop 9)))
#eval IO.println "MIDDLE_BODY"
#eval IO.println (repr (firstBlockBody (firstBlockBody (decodeSuccessAfterAlloc.drop 9))))
#eval IO.println "INNER_BODY"
#eval IO.println (repr (firstBlockBody (firstBlockBody (firstBlockBody (decodeSuccessAfterAlloc.drop 9)))))
