# Mergesort `func10` (absolute 13, `talos_stdio::read`)

Thin adapter `(pointer,length) -> count`.  Its caller has top-first operands
`[length,pointer]`.  The body pushes `length` and then `pointer`, producing the
direct-import top-first list `[pointer,length]`; host reversal then invokes
`stdio.read` as `(length,pointer)`.  `func3` calls it only with the 256-byte chunk
buffer.  The main contract bridges an owned writable `ByteSlice` and
stream state to the exact Universal read transfer.  If
`count=min(length,input.length)`, the returned buffer is
`input.take count ++ oldBuffer.drop count`, host input becomes
`input.drop count`, and output/OOM/buffer suffix are preserved.  There is no
trap under the owned in-bounds range precondition.

The only call sites are the two syntactic positions in `func3` implementing
the same read loop, both `(frame+12,256)`.  Their termination measure uses the
strictly smaller remaining input after nonzero count.  Constant shim overhead
plus host work linear in count.
